{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveLift #-}

module Generate where
import Test.QuickCheck
import ElimTerm
import Term
import Types
import Events
import Control.Monad.State as ST
import Control.Monad (when, foldM)
import Test.Hspec
import PartialOrder as PO
import Basic.Sem
import Basic.Stream
import Control.Monad (replicateM)
import Language.Haskell.TH.Syntax
import List.Sem
import GHC.Arr (lessSafeIndex)
import Debug.Trace (trace)


data Binding = Atom String Ty | Pair String Ty String Ty deriving (Eq,Ord,Show,Lift)
data LR = L | R | NA deriving (Eq, Ord, Show)

data PossibleTerm's = HCatR | HPlusR | HCatL | HPlusL | HLet | HVar | HInt | HEps | HNil | HCons | HStarL

type Ctx = [Binding]

data Error = TypeMismatch
           | OrderViolation (Maybe String) (Maybe String) String
           | NotImplemented Term 
           | LookupFailed String
           deriving (Show, Eq, Ord)

extractBindings :: Ctx -> [(String, Ty)]
extractBindings = concatMap extractBinding
  where
    extractBinding :: Binding -> [(String, Ty)]
    extractBinding (Atom x ty)      = [(x, ty)]
    extractBinding (Pair x1 ty1 x2 ty2) = [(x1, ty1), (x2, ty2)]

genTy :: Gen Ty
genTy = sized go
  where
    go 0 = frequency [(1, return TyEps), (4, return TyInt)] 
    go n = frequency [ (1, TyCat <$> go (n `div` 8) <*> go (n `div` 8)) 
                     , (1, TyPlus <$> go (n `div` 8) <*> go (n `div` 8))
                     , (1, TyStar <$> go (n `div` 8))                   
                     , (1, return TyEps)                       
                     , (4, return TyInt)]                               

fresh :: StateT (Int, Ctx, [String]) Gen String
fresh = do
    (n, ctx, ctx') <- get
    let x = "x_" ++ show (n + 1)
    put (n + 1, ctx, ctx')
    return x

safeConcat :: Ctx -> Ctx -> Ctx
safeConcat ctx1 ctx2 =
  let
    allBindings1 = extractBindings ctx1
    allBindings2 = extractBindings ctx2
    
    vars1 = map fst allBindings1
    vars2 = map fst allBindings2

    duplicates = [x | x <- vars1, x `elem` vars2]
  in
    if null (duplicates)
    then ctx1 ++ ctx2
    else error $ "Duplicate bindings found: " ++ show duplicates

replaceElement :: Ctx -> String -> StateT (Int, Ctx, [String]) Gen ()
replaceElement ctx' x = do
  (n, ctx, extendedCtx) <- get
  let combinedCtx = replaceElement' ctx x ctx'
  put (n, combinedCtx, extendedCtx)

replaceElement' :: Ctx -> String -> Ctx -> Ctx
replaceElement' ctx x ctx' =
  let (ctx0, rest) = break (matches x) ctx
      ctx1 = case rest of
               [] -> []              
               (_ : rest') -> rest'
  in safeConcat (safeConcat ctx0 ctx') ctx1

matches :: String -> Binding -> Bool
matches x (Atom var _) = var == x
matches x (Pair var1 _ var2 _) = var1 == x || var2 == x

lookup' :: Ctx -> String -> Either Error (Ty, PO.Pairs)
lookup' [] x = Left $ LookupFailed x
lookup' (Atom k v : rest) x
    | k == x = Right (v, PO.singleton (x, x))
    | otherwise = lookup' rest x
lookup' (Pair k1 v1 k2 v2 : rest) x
    | k1 == x = Right (v1, PO.singleton (k1, k1))
    | k2 == x = Right (v2, PO.singleton (k2, k2)) 
    | otherwise = lookup' rest x

bind :: Ty -> StateT (Int, Ctx, [String]) Gen String
bind s = do
  x <- fresh
  add (Atom x s)
  return x

replace :: Ctx -> StateT (Int, Ctx, [String]) Gen ()
replace ctx' = do
  (n, _, ctx'') <- get
  put (n, ctx', ctx'')

add :: Binding -> StateT (Int, Ctx, [String]) Gen ()
add el = do
  (n, ctx, ctx') <- get
  put (n, safeConcat ctx [el], ctx')

split :: StateT (Int, Ctx, [String]) Gen (Ctx, Ctx)
split = do
  (_, ctx, _) <- get
  n <- ST.lift $ choose (0, length ctx)
  let ctx0 = take n ctx
  let ctx1 = drop n ctx
  return (ctx0, ctx1)

splitAndInsert :: Ctx -> StateT (Int, Ctx, [String]) Gen ()
splitAndInsert ctx = do
  (ctx0, ctx1) <- split
  replace $ safeConcat (safeConcat ctx0 ctx) ctx1

-- When we've hit 0, generate some concrete type, with no holes.
leaf :: StateT (Int, Ctx, [String]) Gen (Term, Ty)
leaf = do
  (_, ctx, ctx') <- get
  -- Get the current list of bindings.
  let ctxList = extractBindings ctx
  -- If the context is empty, we can create a new binding in it, or we can return an
  -- integer or epsilon type.
  s <- ST.lift genTy
  choice <- ST.lift $ oneof [return TyInt, return TyEps, return s]
  x <- fresh
  case choice of 
    TyInt -> do
      int <- IntR <$> ST.lift arbitrary
      return (int, TyInt)
    TyEps -> return (EpsR, TyEps)
    _ -> do
      add (Atom x s)
      return (Var x s, s)

leftOrRight :: Gen LR
leftOrRight = do elements [L, R]

dequeue :: StateT (Int, Ctx, [String]) Gen (Maybe String)
dequeue = do
  (n, ctx, ctx') <- get
  case ctx' of
    []     -> return Nothing         
    (x:xs) -> do
      put (n, ctx, xs)               
      return (Just x)               

enqueue :: String -> StateT (Int, Ctx, [String]) Gen ()
enqueue x = do
  (n, ctx, ctx') <- get 
  put (n, ctx, ctx' ++ [x])

genTerm :: Maybe Ty -> Gen ((Term, Ty), (Int, Ctx, [String]))
genTerm maybeTy = sized (\n -> runStateT (go maybeTy R n) (0, [], []))
  where
    cons :: Maybe Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    cons t n = do
      ty <- case t of
              Just given -> return given
              Nothing -> ST.lift genTy
      let initialAcc = Nil (TyStar ty)
      let loop acc curN = 
            if curN <= 0
            then return acc
            else do
              choice <- ST.lift $ frequency [(3, return True), (1, return False)]
              choice' <- ST.lift $ frequency [(2, return R), (1, return L)]
              if not choice
              then return acc -- Break early by returning the accumulated term.
              else do
                (gamma, delta) <- split
                replace gamma
                (e, s) <- go (Just ty) choice' (curN `div` 2)
                (_, gamma', _) <- get
                replace (safeConcat gamma' delta)
                loop (Cons e acc) (curN - 1)
      result <- loop initialAcc (n - 1)
      return (result, TyStar ty)
    nil :: Maybe Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    nil t n = do
      ty <- case t of
              Just given -> return given
              Nothing -> ST.lift genTy
      return (Nil ty, ty)
    starCase :: Maybe Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    starCase t n = do
      ty <- case t of
            Just given -> return given
            Nothing -> ST.lift genTy
      z <- fresh
      x <- fresh
      xs <- fresh

      lr <- ST.lift $ leftOrRight
      (e, _) <- go (Just ty) lr (n `div` 2)
      s <- ST.lift $ genTy

      splitAndInsert [Pair x s xs (TyStar s)]
      lr' <- ST.lift $ leftOrRight
      (es, _) <- go (Just ty) lr' (n `div` 2)

      replaceElement [Atom z (TyStar s)] x

      return (StarCase z e x xs es, ty)
    catR :: Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    catR n = do
      (gamma, delta) <- split
      replace gamma
      (x, s) <- go Nothing NA (n `div` 4)
      (_, gamma', _) <- get
      replace delta
      (y, t) <- go Nothing NA (n `div` 4)
      (_, delta', _) <- get
      replace (safeConcat gamma' delta')
      return (CatR x y, TyCat s t)
    plusR :: Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    plusR n = do
      choice <- ST.lift $ oneof [return True, return False]
      case choice of
        True -> do
          t <- ST.lift $ genTy
          (e1, s) <- go Nothing NA (n `div` 4)
          return (InL e1 (TyPlus s t), TyPlus s t)
        False -> do
          s <- ST.lift $ genTy
          (e2, t) <- go Nothing NA (n `div` 4)
          return (InR e2 (TyPlus s t), TyPlus s t)
    var :: Maybe Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    var (Just r) _ = do
      x <- fresh
      add (Atom x r)
      return (Var x r, r)
    var Nothing n = do
      s <- ST.lift $ genTy
      x <- fresh
      add (Atom x s)
      return (Var x s, s)
    catL :: Maybe Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    catL (Just r) n = do
        x <- fresh
        y <- fresh
        z <- fresh

        s <- ST.lift $ genTy
        t <- ST.lift $ genTy

        splitAndInsert [Pair x s y t]
        lr <- ST.lift $ leftOrRight
        (e, _) <- go (Just r) lr (n `div` 2)

        replaceElement [Atom z (TyCat s t)] x
        return (CatL x y z e, r)
    catL Nothing n = do
      s <- ST.lift $ genTy
      t <- ST.lift $ genTy

      x <- fresh
      y <- fresh

      splitAndInsert [Pair x s y t]
      (e, r) <- go Nothing NA (n `div` 4)

      z <- fresh
      replaceElement [Atom z (TyCat s t)] x
      return (CatL x y z e, r)
    let' :: Maybe Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    let' r n = do
        x <- fresh

        (gamma0, temp) <- split
        replace temp
        (delta, gamma1) <- split

        replace delta
        (e, s) <- go Nothing R (n `div` 2)
        (_, delta', _) <- get

        replace (safeConcat (safeConcat gamma0 [Atom x s]) gamma1)
        (e', r) <- go r R (n `div` 2)

        replaceElement delta' x
        return (Let x s e e', r)
    plus :: Maybe Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    plus (Just r) n = do
        x <- fresh
        y <- fresh
        z <- fresh

        s <- ST.lift $ genTy
        t <- ST.lift $ genTy

        splitAndInsert [Atom x s]
        lr <- ST.lift $ leftOrRight
        (e1, _) <- go (Just r) lr (n `div` 2)
      
        replaceElement [Atom y t] x
      
        lr' <- ST.lift $ leftOrRight
        (e2, _) <- go (Just r) lr' (n `div` 2)
      
        replaceElement [Atom z (TyPlus s t)] y
        return (PlusCase z x e1 y e2, t)
    plus Nothing n = do
      s <- ST.lift $ genTy
      t <- ST.lift $ genTy

      x <- fresh
      y <- fresh

      splitAndInsert [Atom x s]
      
      (e1, r1) <- go Nothing NA (n `div` 4)

      replaceElement [Atom y t] x
      lr <- ST.lift leftOrRight
      (e2, _) <- go (Just r1) lr (n `div` 4)

      z <- fresh
      replaceElement [Atom z (TyPlus s t)] y
      return (PlusCase z x e1 y e2, r1)
    lCases :: Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    lCases r n = do
      v <- var (Just r) n
      c <- catL (Just r) n
      l <- let' (Just r) n
      p <- plus (Just r) n
      ST.lift $ frequency
        [ (1, return v),
          (1, return c),
          (1, return l),
          (1, return p)
        ]
    go :: Maybe Ty -> LR -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    go (Just TyEps) _ _ = return (EpsR, TyEps)
    go (Just TyInt) _ _ = do
      tm <- IntR <$> ST.lift arbitrary
      return (tm, TyInt)
    go (Just r) _ 0 = do
      do
        x <- fresh
        add (Atom x r)
        return (Var x r, r)
    go (Just r) L n = lCases r (n - 1)
    go (Just (TyCat s t)) R n = do
      (gamma, delta) <- split
      replace gamma
      (e1, _) <- go (Just s) R (n `div` 2)
      (_, gamma', _) <- get
      replace delta
      (e2, _) <- go (Just t) R (n `div` 2)
      (_, delta', _) <- get
      replace (safeConcat gamma' delta')
      return (CatR e1 e2, TyCat s t)
    go (Just (TyPlus s t)) R _ = do
      x <- fresh
      add (Atom x (TyPlus s t))
      return (Var x (TyPlus s t), TyPlus s t)
    go (Just (TyStar s)) R n = do
      choice <- ST.lift $ frequency [
        (5, return HCons),
        (2, return HNil)]
      case choice of
        HCons -> cons (Just s) (n - 1)
        HNil -> nil (Just (TyStar s)) (n - 1)
        _ -> error ""
    go Nothing _ 0 = do leaf
    go Nothing _ n = do
      choice <- ST.lift $ frequency
        [ (5, return HCatR),
          (5, return HCatL),
          (7, return HPlusR),
          (5, return HPlusL),
          (2, return HNil),
          (5, return HCons),
          (5, return HStarL),
          (5, return HLet),
          (5, return HVar),
          (2, return HInt),
          (2, return HEps)
        ]
      case choice of
        HCatR -> catR (n - 1)
        HCatL -> catL Nothing (n - 1)
        HPlusR -> plusR (n - 1)
        HPlusL -> plus Nothing (n - 1)
        HLet -> let' Nothing (n - 1)
        HVar -> var Nothing (n - 1)
        HInt -> do
          int <- IntR <$> ST.lift arbitrary
          return (int, TyInt)
        HEps -> return (EpsR, TyEps)
        HNil -> nil Nothing (n - 1)
        HCons -> cons Nothing (n - 1)
        HStarL -> starCase Nothing (n - 1)
    go maybeTy lr n = do
      (curN, ctx, ctx') <- get
      error $ trace ("Reached undefined case with parameters:\n" ++
                    "maybeTy: " ++ show maybeTy ++ "\n" ++
                    "LR: " ++ show lr ++ "\n" ++
                    "n: " ++ show n ++ "\n" ++
                    "State: " ++ show (curN, ctx, ctx')) "Unreachable code in go function"