{-# LANGUAGE GADTs #-}

module Main where

import Data.Maybe (mapMaybe)
import Types
import Test.QuickCheck
import ElimTerm
import Events
import Data.Foldable (toList)
import Control.Monad.State
import Control.Monad (when)
import Data.List (nub, (\\))
import Test.Hspec.QuickCheck
import Test.Hspec
import Test.QuickCheck
import Data.List (elemIndex)

type Ctx = [(String, Ty)]
data Term where
    {-
    --------------
    G |- EpsR : eps
    -}
    EpsR :: Term
    {-
    -----------------------
    G;x:s;G' |- Var x s : s
    -}
    Var :: String -> Ty -> Term
    {-
    -----------------
    G |- IntR n : Int
    -}
    IntR :: Int -> Term
    {-
    G' |- e1 : s
    y:Int;G' |- e2 : s
    ------------------------------------
    G;x:Int;G' |- IntCase x e1 y e2 : s
    -}

    {-
    G;x:s;y:t;G' |- e : r
    ----------------------------
    G;z:s.t;G' |- CatL x y z e : r
    -}
    CatL :: String -> String -> String -> Term -> Term
    {-
    G |- e1 : s
    D |- e2 : t
    ----------------------
    G;D |- (e1;e2) : s . t
    -}
    CatR :: Term -> Term -> Term
    {-
    -}
    InL :: Term -> Term
    InR :: Term -> Term
    --          z,        x,        e1,     y,        e2
    PlusCase :: String -> String -> Term -> String -> Term -> Term
    Nil :: Term
    Cons :: Term -> Term -> Term
    StarCase :: String -> Term -> String -> String -> Term -> Term
    -- Wait :: String -> Ty -> Term -> Term
    {-
        D |- e : s      G;x:s;G' |- e' : r
        ------------------------------------
        G;D;G' |- let x = e in e' : r
    -}
    -- a    x,        e,      e' 
    Let :: String -> Term -> Term -> Term
    Fix :: Term -> Term
    Rec :: Term
    deriving (Eq,Ord,Show)

genTy :: Gen Ty
genTy = sized go
  where
    go 0 = frequency [(1, return TyEps), (5, return TyInt)]
    go n = frequency [ (2, TyCat <$> go (n `div` 2) <*> go (n `div` 2))
                     , (2, TyPlus <$> go (n `div` 2) <*> go (n `div` 2))
                     , (2, TyStar <$> go (n `div` 2))
                     , (1, return TyEps)
                     , (1, return TyInt)]

-- Create a fresh variable and return it.
fresh :: StateT (Int, Ctx) Gen String
fresh = do
    (n, ctx) <- get
    let x = "y_" ++ show (n + 1)
    put (n + 1, ctx)
    return x

-- Add a binding to the context.
add :: (String, Ty) -> StateT (Int, Ctx) Gen ()
add el = do
  (n, ctx) <- get
  put (n, safeConcat ctx [el])

safeConcat :: Ctx -> Ctx -> Ctx
safeConcat ctx1 ctx2 =
  let duplicates = [x | (x, _) <- ctx1, x `elem` map fst ctx2]
  in if null (duplicates)
     then ctx1 ++ ctx2
     else error $ "Duplicate bindings found: " 
     ++ show duplicates 

-- Replace the context with a new context.
replace :: Ctx -> StateT (Int, Ctx) Gen ()
replace ctx' = do
  (n, _) <- get
  put (n, ctx')

replaceElement :: String -> Ctx -> StateT (Int, Ctx) Gen ()
replaceElement x ctx' = do
  (_, ctx) <- get
  let (ctx0, rest) = break (\(b, _) -> b == x) ctx
  let ctx1 = case rest of
        [] -> []              
        (_ : rest') -> rest'      
  replace $ (safeConcat (safeConcat ctx0 ctx') ctx1)

-- See if there's a binding of some type in the context already.
lookupByType :: Ctx -> Ty -> Maybe String
lookupByType [] _ = Nothing
lookupByType ((var, ty) : rest) targetTy
  | ty == targetTy = Just var
  | otherwise = lookupByType rest targetTy

-- Create a binding of a certain type, add it to the context, and return
-- the name.
binding :: Ty -> StateT (Int, Ctx) Gen String
binding s = do
  x <- fresh
  add (x, s)
  return x

lookupOrBind :: Ty -> StateT (Int, Ctx) Gen String
lookupOrBind s = do
  (_, ctx) <- get
  case lookupByType ctx s of
    Just x -> return x
    Nothing -> do
      x <- binding s
      return x

split :: StateT (Int, Ctx) Gen (Ctx, Ctx)
split = do
  (_, ctx) <- get
  n <- lift $ choose (0, length ctx)
  
  let ctx0 = take n ctx
  let ctx1 = drop n ctx
  
  return (ctx0, ctx1)

fillHole :: Ctx -> StateT (Int, Ctx) Gen Ctx
fillHole ctx = do
  (_, ctx') <- get
  n <- lift $ choose (0, length ctx')
  
  let ctx0 = take n ctx'
  let temp = drop n ctx'
  
  n' <- lift $ choose (0, length temp)
  let delta = take n' temp
  let ctx1 = drop n' temp

  let newCtx = safeConcat (safeConcat ctx0 ctx) ctx1
  replace newCtx

  return delta

splitAndInsert :: Ctx -> StateT (Int, Ctx) Gen ()
splitAndInsert ctx = do
  (ctx0, ctx1) <- split
  replace $ safeConcat (safeConcat ctx0 ctx) ctx1

choose' :: Monad m => m Bool -> m a -> m a -> m a
choose' bools opt1 opt2 = do
  choice <- bools
  if choice then opt1 else opt2

genTm :: Ty -> Ctx -> Int -> Gen (Term, (Int, Ctx))
genTm ty ctx0 counter0 = sized (\n -> runStateT (go ty n) (counter0, ctx0))
  where
    go :: Ty -> Int -> StateT (Int, Ctx) Gen Term
    -- EpsR
    go TyEps _ = return EpsR
    -- IntR
    go TyInt _ = IntR <$> lift arbitrary
    -- Oops, we bottomed out, make something up?
    go (TyPlus s t) 0 = do
      x <- lookupOrBind (TyPlus s t)
      return $ Var x (TyPlus s t)
    go (TyPlus s t) n = do
      choice <- lift $ elements [True, False]
      if choice
        then do
          choice' <- lift $ elements [True, False]
          if choice'
            then InL <$> go s (n `div` 2)  -- InL
            else InR <$> go t (n `div` 2)  -- InR
        else
          go' (TyPlus s t) n
    -- CatR
    go (TyCat s t) 0 = do
      x <- lookupOrBind (TyCat s t)
      return $ Var x (TyCat s t)
    go (TyCat s t) n = do
      choice <- lift $ elements [True, False]
      if choice 
        then do
          (gamma, delta) <- split
          replace gamma
          e1 <- go s (n `div` 2)
          (_, gamma') <- get
          replace delta
          e2 <- go t (n `div` 2)
          (_, delta') <- get
          replace (safeConcat gamma' delta')
          return $ CatR e1 e2
        else
          go' (TyCat s t) n
    go (TyStar s) 0 = return $ Nil
    go (TyStar s) n = do
      choice <- lift $ elements [True, False]
      if choice
        then do
            choice' <- lift $ elements [True, False]
            if choice'
                then return $ Nil                                                       -- Nil
                else do                                                                                 -- Cons
                    (gamma, delta) <- split
                    replace gamma
                    e1 <- go s (n `div` 2)
                    (_, gamma') <- get
                    replace delta
                    e2 <- go (TyStar s) (n `div` 2)
                    (_, delta') <- get
                    replace (gamma' ++ delta')
                    return $ Cons e1 e2
        else
            go' (TyStar s) n
    go' :: Ty -> Int -> StateT (Int, Ctx) Gen Term
    go' r 0 = do
      x <- lookupOrBind r
      return $ Var x r
    go' r n = do
      choice <- lift $ elements [1..5]
      case choice of
        1 -> do                                                                                       -- PlusCase
          x <- fresh
          s <- lift genTy
          splitAndInsert [(x, s)]
          e1 <- go r (n `div` 2)
          y <- fresh
          t <- lift genTy
          replaceElement x [(y, t)]
          e2 <- go r (n `div` 2)
          z <- fresh
          replaceElement y [(z, TyPlus s t)]
          return $ PlusCase z x e1 y e2
        2 -> do                                                                                         -- VarR
            x <- lookupOrBind r
            return $ Var x r
        3 -> do                                                                                         -- CatL
          -- x : s
          x <- fresh
          s <- lift genTy
          -- y : t
          y <- fresh
          t <- lift genTy
          splitAndInsert [(x, s), (y, t)]
          e <- go r (n `div` 2)
          z <- fresh
          replaceElement x [(z, TyCat s t)]
          replaceElement y []
          return $ CatL x y z e
        4 -> do
          e1 <- go r (n `div` 2)
          x <- fresh
          xs <- fresh
          s <- lift genTy
          splitAndInsert [(x, s), (xs, TyStar s)]
          e2 <- go r (n `div` 2)
          z <- fresh
          replaceElement x [(z, TyStar s)]
          replaceElement xs []
          return $ StarCase z e1 x xs e2
        5 -> do
          x <- fresh
          s <- lift genTy
          delta <- fillHole [(x, s)]
          e' <- go s (n `div` 2)
          (_, ctx') <- get
          replace delta
          e <- go s (n `div` 2)
          (_, delta') <- get
          replace ctx'
          replaceElement x delta'
          return $ Let x e e'
        _ -> error ""

lookup :: Ctx -> String -> Maybe Ty
lookup [] _ = Nothing
lookup ((k, v) : rest) x
    | k == x = Just v
    | otherwise = Main.lookup rest x

getIndices :: Ctx -> [String] -> [Int]
getIndices ctx vars = mapMaybe (`toIndex` ctx) vars

toIndex :: String -> Ctx -> Maybe Int
toIndex x ctx = elemIndex x (map fst ctx)

ordered :: Ctx -> [String] -> [String] -> Bool
ordered ctx vars1 vars2 =
    let idxs1 = getIndices ctx vars1
        idxs2 = getIndices ctx vars2
    in all (\hidx -> all (hidx <) idxs2) idxs1

{-
check :: Ctx -> Term -> Either String (Ty, [String])
check _ (EpsR) = return (TyEps, [])
check _ (IntR _) = return (TyInt, [])
check _ (Nil s) = return (TyStar s, [])

check ctx (Var x s) = 
  case Main.lookup ctx x of
    Just v -> if v == s 
      then 
        return (s, [x])
      else
        Left $ "Type error in variable use. The expected type was " ++ show s ++ ", but the type in the context was " ++ show v ++ "."
    Nothing -> Left $ "Variable " ++ x ++ " not found in context."
check ctx (CatR e1 e2) = do
  (s, e1uses) <- check ctx e1
  (t, e2uses) <- check ctx e2
  if ordered ctx e1uses e2uses
    then
      return ((TyCat s t), (e1uses ++ e2uses))
    else
      Left $ "Interleaved uses in concatenation."
check ctx (CatL x y z e) = undefined
check ctx (Cons e es) = do
  (ht, huses) <- check ctx e
  (tt, tuses) <- check ctx es
  case tt of
    (TyStar et) -> if et == ht -- Element type matches head type.
      then
        if ordered ctx huses tuses
        then return (TyStar et, huses ++ tuses)
        else Left $ "Head and tail variables are interleaved."
      else
        Left $ "Head type, " ++ show ht ++ " doesn't match element type, " ++ show et ++ "."
    _ -> Left $ "Tail not a list, instead it is a " ++ show tt ++ "!"
check ctx (StarCase z e x xs es) = undefined
check ctx (InL e) = undefined
check ctx (InR e) = undefined
check ctx (PlusCase z x e1 y e2) = undefined

check ctx (Let x e e') = undefined

check ctx (Rec) = error "We don't know how to think about Rec yet."
check ctx (Fix e) = error "We don't know how to think about Fix yet."


-- Property: All generated terms should pass the type checker.
prop_checks :: Property
prop_checks = forAll genTy $ \ty ->
    forAll (sized (\n -> genTm ty [] 0)) $ \(term, _) ->
        case check [] term of
            Right _ -> True   -- Type checking succeeded.
            Left _ -> False   -- Type checking failed.
-}

main :: IO ()
main = do
  putStrLn "\nType:"
  -- Generate a random type
  ty <- generate genTy
  print ty
  
  -- Generate a term and retrieve the final context and counter using genTm
  (term, (finalCounter, finalCtx)) <- generate (genTm ty [] 0)
  
  -- Print the generated term
  putStrLn "\nTerm:"
  print term
  
  -- Print the final counter
  putStrLn "\nCounter:"
  print finalCounter
  
  -- Print the final context
  putStrLn "\nContext:"
  print finalCtx
