
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveLift #-}

module Main where

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
    genResult <- generate $ genTerm' Nothing
    let ((term, ty), (_, ctx)) = genResult

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
