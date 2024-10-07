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
    (n, ctx) <- get
    let x = "x_" ++ show (n + 1)
    put (n + 1, ctx)
    return x

genTm :: Ty -> Ctx -> Int -> Gen Term
genTm ty ctx0 counter0 = sized (\n -> evalStateT (go ty n) (counter0, ctx0))
  where
    go :: Ty -> Int -> StateT (Int, Ctx) Gen Term
    -- EpsR
    go TyEps _ = return EpsR
    -- IntR
    go TyInt _ = IntR <$> lift arbitrary
    -- TSumR1
    go (TyPlus _ _) 0 = return EpsR
    go (TyPlus s t) n = do
      choice <- lift $ elements [True, False]
      if choice
        then do
          choice' <- lift $ elements [True, False]
          if choice'
            then InL <$> go s (n `div` 2)  -- InL
            else InR <$> go t (n `div` 2)  -- InR
        else
          go' (TyPlus s t) (n - 1)

    -- CatR
    go (TyCat _ _) 0 = return EpsR
    go (TyCat s t) n = do
      choice <- lift $ elements [True, False]
      if choice
        then do
            (counter, ctx) <- get
            -- Choose a split in the context.
            n' <- lift $ choose (0, length ctx)
            let gamma = take n' ctx
            let delta = drop (length ctx - n') ctx

            -- In the context gamma, generate e1.
            put (counter, gamma)
            e1 <- go s (n `div` 2)

            -- Retrieve any new bindings.
            (counter', gamma') <- get

            -- Change the context to delta; generate e2.
            put (counter', delta)
            e2 <- go t (n `div` 2)

            -- Retrieve new bindings.
            (counter', delta') <- get

            -- Restore the original context, plus any new bindings.
            put (counter', gamma' ++ delta')

            return $ CatR e1 e2
        else
            go' (TyCat s t) (n - 1)
    go (TyStar _) 0 = return Nil
    go (TyStar s) n = do
      choice <- lift $ elements [True, False]
      if choice
        then do
            choice' <- lift $ elements [True, False]
            if choice'
                then return Nil                                                                         -- Nil
                else do                                                                                 -- Cons
                    -- Choose a split.
                    (counter, ctx) <- get
                    n' <- lift $ choose (0, length ctx)
                    let gamma = take n' ctx
                    let delta = drop (length ctx - n') ctx

                    -- State is gamma; generate e1 : s in this context.
                    put (counter, gamma)
                    e1 <- go s (n `div` 2)

                    -- Retrieve the new context, including any new variable
                    -- bindings.
                    (counter', gamma') <- get

                    -- Replace with delta--but keep the updated counter to
                    -- prevent overlapping variable names.
                    put (counter', delta)

                    -- Generate e2 : s* in context delta.
                    e2 <- go (TyStar s) (n `div` 2)

                    (counter'', delta') <- get

                    -- Restore the original context, plus any new bindings.
                    put (counter'', gamma' ++ delta')

                    -- Done!
                    return $ Cons e1 e2
        else
            go' (TyStar s) (n - 1)
    go' :: Ty -> Int -> StateT (Int, Ctx) Gen Term
    go' _ 0 = return EpsR
    go' r n = do
      choice <- lift $ elements [1..5]
      case choice of
        1 -> do                                                                                         -- PlusCase
            (counter, ctx) <- get
            -- x : s
            s <- lift genTy 
            let x = "x_" ++ show (counter + 1)

            -- Choose a place to insert x : s in the existing context.
            n' <- lift $ choose (0, length ctx)
            let gamma0 = take n' ctx
            let gamma1 = (x, s) : drop (length ctx - n') ctx
            put (counter + 1, gamma0 ++ gamma1)

            -- Generate e1 in the context containing x : s
            e1 <- go r (n `div` 2)

            -- y : t
            (counter, ctx) <- get
            t <- lift genTy
            let y = "x_" ++ show (counter + 1)

            -- Insert y : t where x : s was.
            let ctx' = map (\(v, ty') -> if v == x then (y, t) else (v, ty')) ctx
            put (counter + 1, ctx')

            -- Generate e2.
            e2 <- go r (n `div` 2)

            -- z : s + t
            (counter, ctx) <- get
            let z = "x_" ++ show (counter + 1)

            -- Insert z : s + t where y : t was.
            let ctx' = map (\(v, ty') -> if v == y then (z, TyPlus s t) else (v, ty')) ctx
            put (counter + 1, ctx')

            -- Finally done...
            return $ PlusCase z x e1 y e2
        2 -> do                                                                                         -- VarR
            (counter, ctx) <- get
            -- Is the type we're looking for already in there?
            case lookupByType ctx r of

                -- If it is, return its binding.
                Just x -> return $ Var x r
                
                -- If not, create a new binding and return that.
                Nothing -> do
                    let x = "x_" ++ show (counter + 1)
                    put (counter + 1, (x, r) : ctx)
                    return $ Var x r
        3 -> do                                                                                         -- CatL
            (counter, ctx) <- get

            -- Create bindings for x : s, y : t.
            x <- fresh
            y <- fresh
            s <- lift genTy
            t <- lift genTy
            (counter, ctx) <- get

            -- Choose a split.
            n' <- lift $ choose (0, length ctx)
            let gamma0 = take n' ctx
            let gamma1 = (x, s) : (y, t) : drop (length ctx - n') ctx

            -- Update the context with x : s, y : t inserted.
            put (counter, gamma0 ++ gamma1)

            -- Generate e in that context.
            e <- go r (n `div` 2)

            -- Retrieve new bindings and create fresh variable z.
            (counter, ctx) <- get
            z <- fresh
            (counter, ctx) <- get

            -- Replace one of the new bindings with the binding for z : s . t
            -- ; remove the other.
            let ctx' = map (\(v, ty') -> if v == x then (z, TyCat s t) else (v, ty')) $ filter (\(v, _) -> v /= y) ctx
            put (counter, ctx')

            -- Done...
            return $ CatL x y z e
        4 -> do                                                                                         -- StarCase
            -- Run e1 in the current context.
            e1 <- go r (n `div` 2)

            -- This may have added new bindings--retrieve those.
            (counter, ctx) <- get

            -- Generate a new type, s, and fresh variables for
            -- x, xs.
            s <- lift genTy
            x <- fresh
            xs <- fresh
            (counter, ctx) <- get

            -- Choose a random split and insert x, xs.
            n' <- lift $ choose (0, length ctx)
            let gamma0 = take n' ctx
            let gamma1 = (x, s) : (xs, TyStar s) : drop (length ctx - n') ctx
            put (counter, gamma0 ++ gamma1)

            -- Generate e2 in the context containing x : s ; xs : s* ...
            e2 <- go r (n `div` 2)

            -- Create a new binding.
            z <- fresh
            (counter', ctx') <- get

            -- Remove xs : s* ; replace x : s with z : s*.
            let ctx'' = map (\(v, t) -> if v == x then (z, TyStar s) else (v, t)) $ filter (\(v, _) -> v /= xs) ctx'
            put (counter', ctx'')

            return $ StarCase z e1 x xs e2
        5 -> do                                                                                         -- Let
            (counter, ctx) <- get

            -- Choose a split.
            n' <- lift $ choose (0, length ctx)
            let gamma0 = take n' ctx
            let temp = drop (length ctx - n') ctx

            -- Choose a second split...
            n'' <- lift $ choose (0, length temp)
            let delta = take n'' temp
            let gamma1 = drop (length temp - n'') temp

            -- Choose a type for e.
            s <- lift genTy

            -- Generate e : s in context delta.
            put (counter, delta)
            e <- go s (n `div` 2)
            
            -- Create a fresh variable for x, and retrieve any new bindings
            -- within delta.
            x <- fresh
            (counter', delta') <- get

            -- Stitch the context back together, with x : s where delta was.
            put (counter', gamma0 ++ [(x, s)] ++ gamma1)

            -- Generate e' : s in G0 ; x : s ; G1.
            e' <- go s (n `div` 2)
            (counter', gamma') <- get

            -- Remove x : s.
            let (gamma0', rest) = break (\(v, _) -> v == x) gamma'
            let gamma1' = case rest of
                            [] -> []
                            (_:xs) -> xs

            -- Replace with delta'.
            put (counter', gamma0' ++ delta' ++ gamma1')
            return $ Let x e e'
        _ -> error ""

{-
exactSemSpec :: String -> Term -> [TaggedEvent] -> [Event] -> SpecWith ()
exactSemSpec s tm inp outp = it s (
    let eltm = inlineElims tm in
    shouldBe (sToList (denoteElimTerm' eltm (sFromList inp))) outp
 )
-}

-- versionEquivalenceSpec :: String -> Term -> 

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
