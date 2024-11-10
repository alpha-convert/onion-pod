
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveLift #-}

module Main where
import Text.Printf (printf)

import Test.QuickCheck
import qualified Test.Tyche as Tyche
import Term
import Data.List (nub, intersect)
import Test.QuickCheck
import ElimTerm
import Term
import TypeCheck
import Generate
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

import Generate
import TypeCheck
import Control.Monad.State
import System.IO
import Data.Either (isRight, isLeft)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

getConstructor :: Term -> String
getConstructor EpsR = "EpsR"
getConstructor (Var _ _) = "Var"
getConstructor (IntR _) = "IntR"
getConstructor (CatR _ _) = "CatR"
getConstructor (CatL _ _ _ _) = "CatL"
getConstructor (InL _ _) = "InL"
getConstructor (InR _ _) = "InR"
getConstructor (PlusCase _ _ _ _ _) = "PlusCase"
getConstructor (Nil _) = "Nil"
getConstructor (Cons _ _) = "Cons"
getConstructor (StarCase _ _ _ _ _) = "StarCase"
getConstructor (Let _ _ _ _) = "Let"
getConstructor _ = error ""

depth :: Term -> Int
depth EpsR = 1
depth (Var _ _) = 1
depth (IntR _) = 1
depth (CatR e1 e2) = 1 + max (depth e1) (depth e2)
depth (CatL _ _ _ e) = 1 + depth e
depth (InL e _) = 1 + depth e
depth (InR e _) = 1 + depth e
depth (PlusCase _ _ e1 _ e2) = 1 + max (depth e1) (depth e2)
depth (Nil _) = 1
depth (Cons e1 e2) = 1 + max (depth e1) (depth e2)
depth (StarCase _ e1 _ _ e2) = 1 + max (depth e1) (depth e2)
depth (Let _ _ e1 e2) = 1 + max (depth e1) (depth e2)
depth _ = error ""

extractVarsFromTerm :: Term -> [String]
extractVarsFromTerm EpsR = []
extractVarsFromTerm (Var x _) = [x]
extractVarsFromTerm (IntR _) = []
extractVarsFromTerm (CatR e1 e2) = nub $ extractVarsFromTerm e1 ++ extractVarsFromTerm e2
extractVarsFromTerm (CatL _ _ _ e) = extractVarsFromTerm e
extractVarsFromTerm (InL e _) = extractVarsFromTerm e
extractVarsFromTerm (InR e _) = extractVarsFromTerm e
extractVarsFromTerm (PlusCase _ _ e1 _ e2) = nub $ extractVarsFromTerm e1 ++ extractVarsFromTerm e2
extractVarsFromTerm (Nil _) = []
extractVarsFromTerm (Cons e1 e2) = nub $ extractVarsFromTerm e1 ++ extractVarsFromTerm e2
extractVarsFromTerm (StarCase _ e1 _ _ e2) = nub $ extractVarsFromTerm e1 ++ extractVarsFromTerm e2
extractVarsFromTerm (Let _ _ e1 e2) = nub $ extractVarsFromTerm e1 ++ extractVarsFromTerm e2
extractVarsFromTerm _ = error ""

extractVarsFromCtx :: Ctx -> [String]
extractVarsFromCtx ctx = nub [x | Atom x _ <- ctx] ++ [x1 | Pair x1 _ x2 _ <- ctx] ++ [x2 | Pair x1 _ x2 _ <- ctx]

ctxUsed :: Term -> Ctx -> [String]
ctxUsed term ctx =
    let termVars = extractVarsFromTerm term in
    let ctxVars = extractVarsFromCtx ctx in
    termVars `intersect` ctxVars

truncate :: Float -> Float
truncate num = fromIntegral (floor (num * 100)) / 100

calculateProportion :: [String] -> [String] -> Int
calculateProportion termVars ctxVars
    | null ctxVars = 100
    | otherwise = round $ (fromIntegral (length termVars) / fromIntegral (length ctxVars)) * 100

prop_categorizeConstructor :: Property
prop_categorizeConstructor =
    Tyche.visualize "prop_categorizeConstructor" $
        forAll (genTerm Nothing) $ \((term, ty), (_, ctx, _)) ->
            label ("constructor:" ++ getConstructor term) $
                case check ctx term ty of
                    Right _  -> True
                    Left err -> False

prop_depth :: Property
prop_depth =
    Tyche.visualize "prop_depth" $
        forAll (genTerm Nothing) $ \((term, ty), (_, ctx, _)) ->
            label ("depth:" ++ show (depth term)) $
                case check ctx term ty of
                    Right _  -> True
                    Left err -> False

prop_usedVars :: Property
prop_usedVars =
    Tyche.visualize "prop_usedVars" $
        forAll (genTerm Nothing) $ \((term, ty), (_, ctx, _)) ->
            let termVars = ctxUsed term ctx
                ctxVars = extractVarsFromCtx ctx
                proportion = calculateProportion termVars ctxVars
            in label ("used_vars:" ++ show (proportion)) $
                label ("depth:" ++ show (depth term)) $
                label ("constructor:" ++ getConstructor term) $
                case check ctx term ty of
                    Right _  -> True
                    Left err -> False
                    
return []

main :: IO Bool
main = $quickCheckAll

{-
-- Number of terms to generate for testing
testCount :: Int
testCount = 10000

-- Data to track statistics
data Stats = Stats {
    totalTerms :: Int,
    successfulChecks :: Int,
    errorCounts :: Map Error Int
} deriving (Show)

-- Initialize empty stats
emptyStats :: Stats
emptyStats = Stats 0 0 Map.empty

-- Update stats based on the result of a type check
updateStats :: Stats -> Either Error (Ty, PO.Pairs) -> Stats
updateStats stats result = 
    let total = totalTerms stats + 1
    in case result of
        Right _ -> stats { totalTerms = total, successfulChecks = successfulChecks stats + 1 }
        Left err -> stats {
            totalTerms = total,
            errorCounts = Map.insertWith (+) err 1 (errorCounts stats)
        }

-- Generate and type check a term, updating the stats
testTerm :: Stats -> IO Stats
testTerm stats = do
    -- Generate a random term and type pair
    genResult <- generate $ genTerm Nothing
    let ((term, ty), (_, ctx, ctx')) = genResult

    -- Type check the generated term
    let checkResult = check ctx term ty

    -- Update and return the stats
    return $ updateStats stats checkResult

-- Run the test harness and print the results
runTests :: Int -> Stats -> IO Stats
runTests 0 stats = return stats
runTests n stats = do
    updatedStats <- testTerm stats
    runTests (n - 1) updatedStats

-- Print statistics about the test run
printStats :: Stats -> IO ()
printStats stats = do
    let total = totalTerms stats
    let successful = successfulChecks stats
    let failures = total - successful

    putStrLn $ "Total terms generated: " ++ show total
    putStrLn $ "Successfully type checked: " ++ show successful
    putStrLn $ "Failed to type check: " ++ show failures

    -- Print out the error statistics
    putStrLn "Error breakdown:"
    mapM_ (\(err, count) -> putStrLn $ show err ++ ": " ++ show count) (Map.toList $ errorCounts stats)

main :: IO ()
main = do
    putStrLn $ "Running " ++ show testCount ++ " tests..."
    finalStats <- runTests testCount emptyStats
    printStats(finalStats)
-}