module Main where

import Types
import Term
import Test.QuickCheck
import ElimTerm
import Events
import Stream as S1
import StreamC as S2
import StreamCPSStaged
import PullSem as P1
import PullSemCPS as P2
import PullSemCPSStaged
import PullSemCPSStagedImperative
import Data.Foldable (toList)
import Control.Monad.State

import Test.Hspec.QuickCheck
import Test.Hspec
import Test.QuickCheck

type Ctx = [(String, Ty)]
-- data Ty = TyEps | TyInt | TyCat Ty Ty | TyPlus Ty Ty | TyStar Ty deriving (Eq,Ord,Show,Lift)

{-
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
    Let :: String -> Term -> Term -> Term
    Fix :: Term -> Term
    Rec :: Term
    deriving (Eq,Ord,Show)
-}

genCtx :: Gen (Ctx, Int)
genCtx = sized (\n -> runStateT (go n) 0)
  where
    go :: Int -> StateT Int Gen Ctx
    go 0 = return []
    go n = do
        var <- genName
        ty  <- lift genTy
        rest <- go (n - 1)
        return ((var, ty) : rest)

    genName :: StateT Int Gen String
    genName = do
        counter <- get
        put (counter + 1)
        return $ "x_" ++ show (counter + 1)

genTy :: Gen Ty
genTy = sized go
  where
    go 0 = frequency [(1, return TyEps), (5, return TyInt)]
    go n = frequency [ (2, TyCat <$> go (n `div` 2) <*> go (n `div` 2))
                     , (2, TyPlus <$> go (n `div` 2) <*> go (n `div` 2))
                     , (2, TyStar <$> go (n `div` 2))]

fresh :: StateT (Int, Ctx) Gen String
fresh = do
    (n, g) <- get
    let x = "x" ++ (show n)
    put (n + 1, g)
    return x

genTm :: Ty -> Ctx -> Int -> Gen Term
genTm ty ctx0 counter0 = sized (\n -> evalStateT (go ty n) (counter0, ctx0))
  where
    go :: Ty -> Int -> StateT (Int, Ctx) Gen Term
    go TyEps _ = return EpsR
    go TyInt _ = IntR <$> lift arbitrary
    -- TSumR1
    go (TyPlus ty1 ty2) n = do
      choice <- lift $ elements [True, False]
      if choice
        then InL <$> go ty1 (n `div` 2)
        else InR <$> go ty2 (n `div` 2)
    -- TCatR
    go (TyCat ty1 ty2) n = do
        (counter, ctx) <- get
        n' <- lift $ choose (0, length ctx)
        let ctx1 = take n' ctx
        let ctx2 = drop (length ctx - n') ctx
        put (counter, ctx1)
        tm1 <- go ty1 (n `div` 2)
        (counter', ctx') <- get
        put (counter', ctx2)
        tm2 <- go ty2 (n `div` 2)
        (counter'', ctx'') <- get
        put (counter'', ctx' ++ ctx'')
        return $ CatR tm1 tm2
    -- Star cases
    go (TyStar t1) n = do
        choice <- lift $ elements [True, False]  -- Randomly select one of the two branches
        if choice
        then return Nil 
        else do
            (counter, ctx) <- get
            n' <- lift $ choose (0, length ctx)
            let ctx1 = take n' ctx
            let ctx2 = drop (length ctx - n') ctx
            put (counter, ctx1)
            tm1 <- go t1 (n `div` 2)
            (counter', ctx') <- get
            put (counter', ctx2)
            tm2 <- go (TyStar t1) (n `div` 2)
            (counter'', ctx'') <- get
            put (counter'', ctx' ++ ctx'')
            return $ Cons tm1 tm2
    -- SumCase
    go r n = do
        choice <- lift $ elements [True, False]
        if choice
            then do
                (counter, ctx) <- get
                t1 <- lift genTy 
                let x = "x_" ++ show (counter + 1)
                put (counter + 1, (x, t1) : ctx)
                tm1 <- go r (n `div` 2)

                t2 <- lift genTy
                let y = "x_" ++ show (counter + 1)
                let ctx' = map (\(v, t) -> if v == x then (y, t2) else (v, t)) ctx
                put (counter + 1, ctx')
                tm2 <- go r (n `div` 2)

                let z = "x_" ++ show (counter + 1)
                let ctx'' = map (\(v, t) -> if v == y then (z, TyPlus t1 t2) else (v, t)) ctx'
                put (counter + 1, ctx'')

                return $ PlusCase z x tm1 y tm2
            else do
                (counter, ctx) <- get
                case lookupByType ctx r of
                    Just varName -> return $ Var varName r
                    Nothing -> do
                        let newVar = "x_" ++ show (counter + 1)
                        put (counter + 1, (newVar, r) : ctx)
                        return $ Var newVar r

lookupByType :: Ctx -> Ty -> Maybe String
lookupByType [] _ = Nothing
lookupByType ((var, ty) : rest) targetTy
  | ty == targetTy = Just var
  | otherwise = lookupByType rest targetTy

main :: IO ()
main = do
  putStrLn "Generated Contexts:"
  (ctx, counter) <- generate genCtx
  print ctx
  print counter
  
  putStrLn "Generated Types:"
  ty <- generate genTy
  print ty
  
  putStrLn "Generated Terms:"
  sample (genTm ty ctx counter)
