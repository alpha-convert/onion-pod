module MechanicalEquivSpec (spec) where

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

genCtx :: Gen Ctx
genCtx = sized (\n -> evalStateT (go n) 0)
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
                     , (1, TyPlus <$> go (n `div` 2) <*> go (n `div` 2))]

genTm :: Ctx -> Ty -> Gen Term
genTm ctx ty = sized (go ctx ty)
  where
    go :: Ctx -> Ty -> Int -> Gen Term
    go _ TyEps _ = return EpsR
    go _ TyInt _ = IntR <$> arbitrary
    go ctx' (TyPlus ty1 ty2) n =
      oneof [ InL <$> go ctx' ty1 (n `div` 2), 
              InR <$> go ctx' ty2 (n `div` 2)
            -- TODO: PlusCase
            ]
    go _ _ _ = undefined

-- Worry about this later.
genName :: Gen String
genName = elements ["x", "y", "z", "w"]

main :: IO ()
main = do
  -- Generate and print a sample context
  putStrLn "Generated Contexts:"
  ctx <- generate genCtx
  print ctx
  
  -- Generate and print a sample type
  putStrLn "Generated Types:"
  ty <- generate genTy
  print ty
  
  -- Generate and print a sample term
  putStrLn "Generated Terms:"
  sample (genTm ctx ty)

{-
equivSpec :: String -> Spec
equivSpec s = it s $ do
  ctx <- generate genCtx
  ty  <- generate genTy
  
  tm <- generate (genTm ctx ty)
  
  let elimTm = inlineElims tm
  let tevs = genTaggedEventsForContext ctx
  let (S1.S (S1.SF x0 p)) = S1.sFromList tevs
  
  S1.sToList (P1.semElim elimTm (S1.sFromList tevs)) 
    `shouldBe` S2.sToList (P2.semElim elimTm (S2.sFromList tevs))
-}
{-
exactSemSpec :: String -> Term -> [TaggedEvent] -> [Event] -> SpecWith ()
exactSemSpec s tm inp outp = it s (
    let eltm = inlineElims tm in
    shouldBe (sToList (denoteElimTerm' eltm (sFromList inp))) outp
 )
-}

spec :: Spec
spec = undefined