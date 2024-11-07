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

data Binding = Atom String Ty | Pair String Ty String Ty deriving (Eq,Ord,Show,Lift)
data LR = L | R | NA

data PossibleTerm's = HCatR | HPlusR | HCatL | HPlusL | HLet | HVar

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
    go n = frequency [ (1, TyCat <$> go (n `div` 2) <*> go (n `div` 2)) 
                     , (1, TyPlus <$> go (n `div` 2) <*> go (n `div` 2))
                     -- , (1, TyStar <$> go (n `div` 2))                   
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
    var :: Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    var r _ = do
      x <- fresh
      add (Atom x r)
      return (Var x r, r)
    catL :: Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    catL r n = do
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
    let' :: Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    let' r n = do
        x <- fresh

        (gamma0, temp) <- split
        replace temp
        (delta, gamma1) <- split

        replace delta
        (e, s) <- go Nothing R (n `div` 2)
        (_, delta', _) <- get

        replace (safeConcat (safeConcat gamma0 [Atom x s]) gamma1)
        (e', r) <- go (Just r) R (n `div` 2)

        replaceElement delta' x
        return (Let x s e e', r)
    plus :: Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    plus r n = do
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
    lCases :: Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    lCases r n = do
      v <- var r n
      c <- catL r n
      l <- let' r n
      p <- plus r n
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
    go Nothing _ 0 = do leaf
    go Nothing _ n = do
      choice <- ST.lift $ oneof [
        return HCatR, 
        return HCatL,
        return HPlusR,
        return HPlusL, 
        return HLet,
        return HVar]
      case choice of
        HCatR -> do
          (gamma, delta) <- split
          replace gamma
          (x, s) <- go Nothing NA (n `div` 4)
          (_, gamma', ctx') <- get
          replace delta
          (y, t) <- go Nothing NA (n `div` 4)
          (_, delta', ctx') <- get
          replace (safeConcat gamma' delta')
          return (CatR x y, TyCat s t)
        HCatL -> do
          (_, s) <- go Nothing NA (n `div` 4)
          (_, t) <- go Nothing NA (n `div` 4)

          x <- fresh
          y <- fresh

          splitAndInsert [Pair x s y t]
          (e, r) <- go Nothing NA (n `div` 4)

          z <- fresh
          replaceElement [Atom z (TyCat s t)] x
          return (CatL x y z e, r)
        HPlusR -> do
          (e1, s) <- go Nothing NA (n `div` 4)
          (e2, t) <- go Nothing NA (n `div` 4)
          ST.lift $ oneof [return (InL e1 (TyPlus s t), TyPlus s t), return (InR e2 (TyPlus s t), TyPlus s t)]
        HPlusL -> do
          (_, s) <- go Nothing NA (n `div` 4)
          (_, t) <- go Nothing NA (n `div` 4)

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
        HLet -> do
          (gamma', temp) <- split
          replace temp
          (delta, gamma'') <- split
          replace delta

          (e, s) <- go Nothing NA (n `div` 4)
          (_, delta', _) <- get

          x <- fresh
          replace (safeConcat (safeConcat gamma' [Atom x s]) gamma'')
          enqueue x
          (e', t) <- go Nothing NA (n `div` 4)
          replaceElement delta' x

          return (Let x s e e', t)
        HVar -> do
          (_, s) <- go Nothing NA (n `div` 4)
          x <- fresh
          add (Atom x s)
          return (Var x s, s)
    go _ _ _ = undefined

{-
genTerm' :: Maybe Ty -> Gen ((Term, Ty), (Int, Ctx))
genTerm' maybeTy = sized (\n -> runStateT (go maybeTy R n) (0, []))
  where
    {-
    lCases :: Ty -> Int -> StateT (Int, Ctx) Gen (Term, Ty)
    lCases r n = do
        choice <- ST.lift $ elements [1..5]
        case choice of
          1 -> do
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
          2 -> do
            lr <- ST.lift $ leftOrRight
            (_, s) <- go (Just r) lr (n `div` 2)
            x <- fresh
            add (Atom x s)
            return (Var x s, s)
          3 -> do
            z <- fresh
            x <- fresh
            xs <- fresh

            lr <- ST.lift $ leftOrRight
            (e, _) <- go (Just r) lr (n `div` 2)
            s <- ST.lift $ genTy

            splitAndInsert [Pair x s xs (TyStar s)]
            lr' <- ST.lift $ leftOrRight
            (es, _) <- go (Just r) lr' (n `div` 2)

            replaceElement [Atom z (TyStar s)] x

            return (StarCase z e x xs es, r)
          4 -> do
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
          5 -> do
            x <- fresh

            (gamma0, temp) <- split
            replace temp
            (delta, gamma1) <- split

            replace delta
            (e, s) <- go Nothing R (n `div` 2)
            (_, delta') <- get

            replace (safeConcat (safeConcat gamma0 [Atom x s]) gamma1)
            (e', r) <- go (Just r) R (n `div` 2)

            replaceElement delta' x
            return (Let x s e e', r)
          _ -> undefined
    -}
    go :: Maybe Ty -> LR -> Int -> StateT (Int, Ctx) Gen (Term, Ty)
    go (Just TyEps) _ _ = return (EpsR, TyEps)
    go (Just TyInt) _ _ = do
      tm <- IntR <$> ST.lift arbitrary
      return (tm, TyInt)
    go (Just r) L n = do
      x <- fresh
      add (Atom x r)
      return (Var x r, r)
    go (Just (TyStar s)) _ 0 = do
      return (Nil (TyStar s), TyStar s)
    go (Just (TyStar r)) R n = do
      x <- fresh
      add (Atom x (TyStar r))
      return (Var x (TyStar r), TyStar r)
      {-
      do
        (gamma, delta) <- split
        replace gamma
        (e, _) <- go (Just s) R (n + 1)
        (_, gamma') <- get
        replace (safeConcat gamma' delta)
        return (Cons' e (Nil' (TyStar s)), TyStar s)
      -}
    go (Just (TyCat s t)) R n = do
      (gamma, delta) <- split
      replace gamma
      (e1, _) <- go (Just s) R (n `div` 2)
      (_, gamma') <- get
      replace delta
      (e2, _) <- go (Just t) R (n `div` 2)
      (_, delta') <- get
      replace (safeConcat gamma' delta')
      return (CatR e1 e2, TyCat s t)
    go (Just (TyPlus s t)) R n = do
      x <- fresh
      add (Atom x (TyPlus s t))
      return (Var x (TyPlus s t), (TyPlus s t))
      -- lCases (TyPlus s t) (n `div` 2)
      {-
      (e1, _) <- go (Just s) R (n + 1)
      (e2, _) <- go (Just t) R (n + 1)
      ST.lift $ oneof
         [return (InL' e1, TyPlus s t), return (InR' e2, TyPlus s t)]
      -}
    go (Just r) _ 0 = do
        x <- fresh
        add (Atom x r)
        return (Var x r, r)
    go Nothing _ 0 = do leaf
    go Nothing _ n = do
      choice <- ST.lift $ oneof [
        return HCatR', 
        return HCatL', 
        -- return HPlusR, 
        return HPlusL, 
        return HLet',
        -- return HStarR,
        return HStarL,
        return HVar']
      case choice of
        HCatR' -> do
          (gamma, delta) <- split
          replace gamma
          (x, s) <- go Nothing NA (n `div` 4)
          (_, gamma') <- get
          replace delta
          (y, t) <- go Nothing NA (n `div` 4)
          (_, delta') <- get
          replace (safeConcat gamma' delta')
          return (CatR x y, TyCat s t)
        HCatL' -> do
          (_, s) <- go Nothing NA (n `div` 4)
          (_, t) <- go Nothing NA (n `div` 4)

          x <- fresh
          y <- fresh

          splitAndInsert [Pair x s y t]
          (e, r) <- go Nothing NA (n `div` 4)

          z <- fresh
          replaceElement [Atom z (TyCat s t)] x
          return (CatL x y z e, r)
        HStarR -> do
          (gamma, delta) <- split
          replace gamma
          (e, s) <- go Nothing NA (n `div` 4) 
          (_, gamma') <- get
          replace (safeConcat gamma' delta)
          return (Cons e (Nil (TyStar s)), TyStar s)
        HStarL -> do
          (e, r) <- go Nothing NA (n `div` 4)
          (_, s) <- go Nothing NA (n `div` 4)

          x <- fresh
          xs <- fresh
          z <- fresh

          splitAndInsert [Pair x s xs (TyStar s)]
          lr <- ST.lift $ leftOrRight
          (es, _) <- go (Just r) lr (n `div` 4)

          replaceElement [Atom z (TyStar s)] x

          return (StarCase z e x xs es, r)
        HPlusR -> do
          (e1, s) <- go Nothing NA (n `div` 4)
          (e2, t) <- go Nothing NA (n `div` 4)
          ST.lift $ oneof [return (InL e1 (TyPlus s t), TyPlus s t), return (InR e2 (TyPlus s t), TyPlus s t)]
        HPlusL -> do
          (_, s) <- go Nothing NA (n `div` 4)
          (_, t) <- go Nothing NA (n `div` 4)

          x <- fresh
          y <- fresh

          splitAndInsert [Atom x s]
          
          (e1, r1) <- go Nothing NA (n `div` 4)

          replaceElement [Atom y t] x
          lr <- ST.lift $ leftOrRight
          (e2, _) <- go (Just r1) lr (n `div` 4)

          z <- fresh
          replaceElement [Atom z (TyPlus s t)] y
          return (PlusCase z x e1 y e2, r1)
        HLet' -> do
          (gamma', temp) <- split
          replace temp
          (delta, gamma'') <- split
          replace delta

          (e, s) <- go Nothing NA (n `div` 4)
          (_, delta') <- get

          x <- fresh
          replace (safeConcat (safeConcat gamma' [Atom x s]) gamma'')

          (e', t) <- go Nothing NA (n `div` 4)
          replaceElement delta' x

          return (Let x s e e', t)
        HVar' -> do
          (_, s) <- go Nothing NA (n `div` 4)
          x <- fresh
          add (Atom x s)
          return (Var x s, s)
    go _ _ _ = undefined
-}