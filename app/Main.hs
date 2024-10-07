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
                     , (2, TyStar <$> go (n `div` 2))
                     , (1, return TyEps)
                     , (1, return TyInt)]

fresh :: StateT (Int, Ctx) Gen String
fresh = do
    (n, g) <- get
    let x = "x_" ++ show (n + 1)
    put (n + 1, g)
    return x

updateCtx :: Ctx -> StateT (Int, Ctx) Gen ()
updateCtx ctx = do
    (counter, _) <- get
    put (counter, ctx)
    (counter, ctx) <- get
    return ()

updateCounter :: Int -> StateT (Int, Ctx) Gen ()
updateCounter counter = do
    (_, ctx) <- get
    put (counter, ctx)
    (counter, ctx) <- get
    return ()

update :: Ctx -> Int -> StateT (Int, Ctx) Gen ()
update ctx counter = do
    (counter0, ctx0) <- get
    put (counter, ctx)
    (counter, ctx) <- get
    return ()

genTm :: Ty -> Ctx -> Int -> Gen Term
genTm ty ctx0 counter0 = sized (\n -> evalStateT (go ty n) (counter0, ctx0))
  where
    go :: Ty -> Int -> StateT (Int, Ctx) Gen Term
    -- EpsR
    go TyEps _ = return EpsR
    -- IntR
    go TyInt _ = IntR <$> lift arbitrary

    -- TSumR1
    go (TyPlus _ _) 0 = return EpsR  -- base case for recursion
    go (TyPlus ty1 ty2) n = do
      choice <- lift $ elements [True, False]
      if choice
        then do
          choice' <- lift $ elements [True, False]
          if choice'
            then InL <$> go ty1 (n `div` 2)  -- InL
            else InR <$> go ty2 (n `div` 2)  -- InR
        else
          go' (TyPlus ty1 ty2) (n - 1)   -- Ensure recursion depth decreases

    -- CatR
    go (TyCat _ _) 0 = return EpsR  -- base case for recursion
    go (TyCat ty1 ty2) n = do
      choice <- lift $ elements [True, False]
      if choice
        then do
            (counter, ctx) <- get
            n' <- lift $ choose (0, length ctx)
            let ctx1 = take n' ctx
            let ctx2 = drop (length ctx - n') ctx
            updateCtx ctx1
            tm1 <- go ty1 (n `div` 2)
            updateCtx ctx2
            tm2 <- go ty2 (n `div` 2)
            (counter'', ctx'') <- get
            updateCtx (ctx' ++ ctx'')
            return $ CatR tm1 tm2
        else
            go' (TyCat ty1 ty2) (n - 1)  -- Ensure recursion depth decreases

    -- Star cases
    go (TyStar _) 0 = return EpsR  -- base case for recursion
    go (TyStar t1) n = do
      choice <- lift $ elements [True, False]
      if choice
        then do
            choice' <- lift $ elements [True, False]
            if choice'
                then return Nil  -- Nil
                else do
                    (counter, ctx) <- get
                    n' <- lift $ choose (0, length ctx)
                    let ctx1 = take n' ctx
                    let ctx2 = drop (length ctx - n') ctx
                    updateCtx ctx1
                    tm1 <- go t1 (n `div` 2)
                    updateCtx ctx2
                    tm2 <- go (TyStar t1) (n `div` 2)
                    (counter'', ctx'') <- get
                    updateCtx (ctx' ++ ctx'')
                    return $ Cons tm1 tm2
        else
            go' (TyStar t1) (n - 1)  -- Ensure recursion depth decreases

    -- `go'` logic
    go' :: Ty -> Int -> StateT (Int, Ctx) Gen Term
    go' _ 0 = return EpsR  -- base case for recursion
    go' r n = do
      choice <- lift $ elements [1..5]
      case choice of
        -- PlusCase
        1 -> do
            t1 <- lift genTy
            x <- fresh
            ctx <- gets snd
            updateCtx ((x, t1) : ctx)
            tm1 <- go r (n `div` 2)

            t2 <- lift genTy
            y <- fresh
            ctx <- gets snd
            let ctx' = map (\(v, t) -> if v == x then (y, t2) else (v, t)) ctx
            updateCtx ctx'
            tm2 <- go r (n `div` 2)

            z <- fresh
            ctx <- gets snd
            let ctx'' = map (\(v, t) -> if v == y then (z, TyPlus t1 t2) else (v, t)) ctx
            updateCtx ctx''
            return $ PlusCase z x tm1 y tm2

        -- VarR
        2 -> do
            ctx <- gets snd
            case lookupByType ctx r of
                Just varName -> return $ Var varName r
                Nothing -> do
                    newVar <- fresh
                    updateCtx ((newVar, r) : ctx)
                    return $ Var newVar r

        -- CatL
        3 -> do
            t1 <- lift genTy
            x <- fresh
            updateCtx [(x, t1)]
            
            t2 <- lift genTy
            y <- fresh
            updateCtx [(y, t2)]

            e <- go r (n `div` 2)

            z <- fresh
            ctx <- gets snd
            let ctx' = map (\(v, t) -> if v == x then (z, TyCat t1 t2) else (v, t)) $ filter (\(v, _) -> v /= y) ctx
            updateCtx ctx'
            return $ CatL x y z e

        -- StarCase
        4 -> do
            e1 <- go r (n `div` 2)

            -- Choose a random split.
            ctx <- gets snd
            n' <- lift $ choose (0, length ctx)
            let gamma0 = take n' ctx
            let gamma1 = drop (length ctx - n') ctx

            ty1 <- lift genTy
            x <- fresh
            xs <- fresh

            updateCtx (gamma0 ++ [(x, ty1), (xs, TyStar ty1)] ++ gamma1)

            e2 <- go r (n `div` 2)
            z <- fresh

            ctx <- gets snd
            let ctx' = map (\(v, t) -> if v == x then (z, TyStar ty1) else (v, t)) $ filter (\(v, _) -> v /= xs) ctx
            updateCtx ctx'
            return $ StarCase z e1 x xs e2

        -- Let
        5 -> do
            ctx <- gets snd
            n' <- lift $ choose (0, length ctx)
            let gamma0 = take n' ctx
            let temp = drop (length ctx - n') ctx

            n'' <- lift $ choose (0, length temp)
            let delta = take n'' temp
            let gamma1 = drop (length temp - n'') temp

            s <- lift genTy
            updateCtx delta

            e <- go ty (n `div` 2)
            x <- fresh
            updateCtx (gamma0 ++ [(x, s)] ++ gamma1)

            e' <- go r (n `div` 2)
            ctx <- gets snd
            let (gamma0', rest) = break (\(v, _) -> v == x) ctx
            let gamma1' = case rest of
                            [] -> []
                            (_:xs) -> xs
            updateCtx (gamma0' ++ delta ++ gamma1')
            return $ Let x e e'

        _ -> error "Invalid choice"

{-
exactSemSpec :: String -> Term -> [TaggedEvent] -> [Event] -> SpecWith ()
exactSemSpec s tm inp outp = it s (
    let eltm = inlineElims tm in
    shouldBe (sToList (denoteElimTerm' eltm (sFromList inp))) outp
 )
-}

lookupByType :: Ctx -> Ty -> Maybe String
lookupByType [] _ = Nothing
lookupByType ((var, ty) : rest) targetTy
  | ty == targetTy = Just var
  | otherwise = lookupByType rest targetTy

main :: IO ()
main = do
  -- putStrLn "Generated Contexts:"
  (ctx, counter) <- generate genCtx
  -- print ctx
  -- print counter
  
  -- putStrLn "Generated Types:"
  ty <- generate genTy
  
  
  putStrLn "Generated Terms:"
  sample (genTm ty [] counter)

  putStrLn "Generated Types:"
  print ty
