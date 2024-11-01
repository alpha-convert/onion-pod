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

data Binding = Atom String Ty | Pair String Ty String Ty deriving (Eq,Ord,Show,Lift)
data LR = L | R | NA

-- Arguments are always holes.
data PossibleTerm's = HCatR' | HPlusR | HStarR | HStarL | HCatL' | HPlusL | HLet' | HVar'

type Ctx = [Binding]

data Error = TypeMismatch
           | OrderViolation (Maybe String) (Maybe String) String
           | NotImplemented Term 
           | LookupFailed String
           | UnfilledHole
           deriving (Show, Eq)

extractBindings :: Ctx -> [(String, Ty)]
extractBindings = concatMap extractBinding
  where
    extractBinding :: Binding -> [(String, Ty)]
    extractBinding (Atom x ty)      = [(x, ty)]
    extractBinding (Pair x1 ty1 x2 ty2) = [(x1, ty1), (x2, ty2)]

-- Top-level is always not a hole.
genTy :: Gen Ty
genTy = sized go
  where
    go 0 = frequency [(1, return TyEps), (4, return TyInt)] -- Favor base types heavily
    go n = frequency [ (1, TyCat <$> go (n `div` 2) <*> go (n `div` 2))  -- Reduce recursion depth
                     , (1, TyPlus <$> go (n `div` 2) <*> go (n `div` 2)) -- Reduce recursion depth
                     , (1, TyStar <$> go (n `div` 2))                    -- Reduce recursion depth
                     , (1, return TyEps)                                 -- Favor base types
                     , (4, return TyInt)]                                -- Favor base types

-- Create a fresh variable and return it.
fresh :: StateT (Int, Ctx) Gen String
fresh = do
    (n, ctx) <- get
    let x = "x_" ++ show (n + 1)
    put (n + 1, ctx)
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

replaceElement :: Ctx -> String -> StateT (Int, Ctx) Gen ()
replaceElement ctx' x = do
  (n, ctx) <- get
  let combinedCtx = replaceElement' ctx x ctx'
  put (n, combinedCtx)

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
    | k == x = Right (v, PO.singleton (x, x))  -- Found variable, return type and PO with (x, x)
    | otherwise = lookup' rest x
lookup' (Pair k1 v1 k2 v2 : rest) x
    | k1 == x = Right (v1, PO.singleton (k1, k1))  -- First variable in pair found
    | k2 == x = Right (v2, PO.singleton (k2, k2))  -- Second variable in pair found
    | otherwise = lookup' rest x

bind :: Ty -> StateT (Int, Ctx) Gen String
bind s = do
  x <- fresh
  add (Atom x s)
  return x

replace :: Ctx -> StateT (Int, Ctx) Gen ()
replace ctx' = do
  (n, _) <- get
  put (n, ctx')

add :: Binding -> StateT (Int, Ctx) Gen ()
add el = do
  (n, ctx) <- get
  put (n, safeConcat ctx [el])

split :: StateT (Int, Ctx) Gen (Ctx, Ctx)
split = do
  (_, ctx) <- get
  n <- ST.lift $ choose (0, length ctx)
  let ctx0 = take n ctx
  let ctx1 = drop n ctx
  return (ctx0, ctx1)

splitAndInsert :: Ctx -> StateT (Int, Ctx) Gen ()
splitAndInsert ctx = do
  (ctx0, ctx1) <- split
  replace $ safeConcat (safeConcat ctx0 ctx) ctx1

-- When we've hit 0, generate some concrete type, with no holes.
leaf :: StateT (Int, Ctx) Gen (Term, Ty)
leaf = do
  (_, ctx) <- get
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
leftOrRight = do
  choice <- elements [L, R]
  return choice

genTerm' :: Maybe Ty -> Gen ((Term, Ty), (Int, Ctx))
genTerm' maybeTy = sized (\n -> runStateT (go maybeTy R n) (0, []))
  where
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
            (e1, _) <- go (Just r) lr (n + 1)
          
            replaceElement [Atom y t] x
          
            lr' <- ST.lift $ leftOrRight
            (e2, _) <- go (Just r) lr' (n + 1)
          
            replaceElement [Atom z (TyPlus s t)] y
            return (PlusCase z x e1 y e2, t)
          2 -> do
            lr <- ST.lift $ leftOrRight
            (_, s) <- go (Just r) lr (n `div` 4)
            x <- fresh
            add (Atom x s)
            return (Var x s, s)
          3 -> do
            z <- fresh
            x <- fresh
            xs <- fresh

            lr <- ST.lift $ leftOrRight
            (e, _) <- go (Just r) lr (n + 1)
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
            (e, _) <- go (Just r) lr (n + 1)

            replaceElement [Atom z (TyCat s t)] x
            return (CatL x y z e, r)
          5 -> do
            x <- fresh

            (gamma0, temp) <- split
            replace temp
            (delta, gamma1) <- split

            replace delta
            (e, s) <- go Nothing R (n + 1)
            (_, delta') <- get

            replace (safeConcat (safeConcat gamma0 [Atom x s]) gamma1)
            (e', r) <- go (Just r) R (n + 1)

            replaceElement delta' x
            return (Let x s e e', r)
          _ -> undefined
    go :: Maybe Ty -> LR -> Int -> StateT (Int, Ctx) Gen (Term, Ty)
    go (Just TyEps) _ _ = return (EpsR, TyEps)
    go (Just TyInt) _ _ = do
      tm <- IntR <$> ST.lift arbitrary
      return (tm, TyInt)
    go (Just r) L n = lCases r n
    go (Just (TyStar s)) _ 0 = do
      return (Nil (TyStar s), TyStar s)
    go (Just (TyStar s)) R n = lCases (TyStar s) n
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
      (e1, _) <- go (Just s) R (n + 1)
      (_, gamma') <- get
      replace delta
      (e2, _) <- go (Just t) R (n + 1)
      (_, delta') <- get
      replace (safeConcat gamma' delta')
      return (CatR e1 e2, TyCat s t)
    go (Just (TyPlus s t)) R n = lCases (TyPlus s t) n
      {-
      (e1, _) <- go (Just s) R (n + 1)
      (e2, _) <- go (Just t) R (n + 1)
      ST.lift $ oneof
         [return (InL' e1, TyPlus s t), return (InR' e2, TyPlus s t)]
      -}
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
