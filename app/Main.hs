
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

generateTaggedEvents :: Ctx -> Gen [TaggedEvent]
generateTaggedEvents ctx = do
    let bindings = extractBindings ctx 
    genTaggedEventsForContext bindings

semElimTerm' :: ElimTerm -> Stream TaggedEvent -> Stream Event
semElimTerm' a (S sf) = S (semElimTerm a sf)

exactSemSpec :: String -> Ctx -> Term -> SpecWith ()
exactSemSpec s ctx tm = it s $ do
    taggedEvents <- generate $ generateTaggedEvents ctx
    
    putStrLn $ "Generated Tagged Events: " ++ show taggedEvents
    
    let eltm = inlineElims tm
    
    let evaluatedEvents = sToList (semElimTerm' eltm (sFromList taggedEvents))
    
    let expectedEvents = List.Sem.bigStepTerm tm taggedEvents
    
    putStrLn $ "Evaluated Events: " ++ show evaluatedEvents
    putStrLn $ "Expected Events: " ++ show expectedEvents
    
    evaluatedEvents `shouldBe` expectedEvents

data ErrorCount = ErrorCount {
    orderViolations   :: Int,
    typeMismatches    :: Int,
    lookupFailures    :: Int,
    notImplemented    :: Int,
    hole              :: Int
} deriving (Show)

categorizeError :: Error -> ErrorCount -> ErrorCount
categorizeError (TypeMismatch) counts = counts { typeMismatches = typeMismatches counts + 1 }
categorizeError (OrderViolation _ _ _) counts     = counts { orderViolations = orderViolations counts + 1 }
categorizeError (LookupFailed _) counts   = counts { lookupFailures = lookupFailures counts + 1 }
categorizeError (NotImplemented _) counts = counts { notImplemented = notImplemented counts + 1 }

initialErrorCount :: ErrorCount
initialErrorCount = ErrorCount 0 0 0 0 0

prop_check_term :: Gen (Either (Error, Term, Ty, Ty, Ctx) (PO.Pairs, Term, Ty, Ty, Ctx))
prop_check_term = do
  ((term, inferredTy), (_, ctx)) <- genTerm' Nothing
  return $ case check ctx term inferredTy of
    Right (ty', pairs) -> Right (pairs, term, TyEps, inferredTy, ctx)
    Left err           -> Left (err, term, TyEps, inferredTy, ctx)

runAndReport :: IO ()
runAndReport = do
  results <- generate (replicateM 100000 prop_check_term)

  (successes, errorCounts, _, failuresList) <- foldM categorizeResult (0, initialErrorCount, [], []) results

  let numFailed = 100000 - successes

  putStrLn "\nFailed Term's and Their Errors:"

  putStrLn $ "\nTotal terms generated: " ++ show 100000
  putStrLn $ "Successful type checks: " ++ show successes
  putStrLn $ "Failed type checks: " ++ show numFailed
  putStrLn $ "Success rate: " ++ show (fromIntegral successes / 100000 * 100) ++ "%"
  putStrLn $ "Failure rate: " ++ show (fromIntegral numFailed / 100000 * 100) ++ "%"

  putStrLn "\nError breakdown:"
  putStrLn $ "Order Violations: " ++ show (orderViolations errorCounts)
  putStrLn $ "Type Mismatches: " ++ show (typeMismatches errorCounts)
  putStrLn $ "Lookup Failures: " ++ show (lookupFailures errorCounts)
  putStrLn $ "Not Implemented Errors: " ++ show (notImplemented errorCounts)

categorizeResult :: (Int, ErrorCount, [(PO.Pairs, Term, Ty, Ty, Ctx)], [(Error, Term, Ty, Ty, Ctx)]) 
                 -> Either (Error, Term, Ty, Ty, Ctx) (PO.Pairs, Term, Ty, Ty, Ctx) 
                 -> IO (Int, ErrorCount, [(PO.Pairs, Term, Ty, Ty, Ctx)], [(Error, Term, Ty, Ty, Ctx)])
categorizeResult (successes, counts, successesList, failuresList) (Right (po, term, originalTy, inferredTy, ctx)) = do
  putStrLn "\nTerm passed type checking:"
  putStrLn $ "Term': " ++ show term
  putStrLn $ "Inferred Type: " ++ show inferredTy
  putStrLn $ "Context: " ++ show ctx

  let taggedEventsGen = generateTaggedEvents ctx 
  taggedEvents <- generate taggedEventsGen

  putStrLn $ "Generated Tagged Events: " ++ show taggedEvents

  let eltm = inlineElims term
  let evaluatedEvents = sToList (semElimTerm' eltm (sFromList taggedEvents))
  let expectedEvents = List.Sem.bigStepTerm term taggedEvents

  putStrLn $ "Evaluated Events: " ++ show evaluatedEvents
  putStrLn $ "Expected Events: " ++ show expectedEvents

  return (successes + 1, counts, (po, term, originalTy, inferredTy, ctx) : successesList, failuresList)

categorizeResult (successes, counts, successesList, failuresList) (Left (err, term, originalTy, inferredTy, ctx)) = do
  putStrLn "----------------------------"
  putStrLn $ "Generated Term': " ++ show term
  putStrLn $ "Inferred Type: " ++ show inferredTy
  putStrLn $ "Context: " ++ show ctx
  putStrLn $ "Error: " ++ show err

  return (successes, categorizeError err counts, successesList, (err, term, originalTy, inferredTy, ctx) : failuresList)

main :: IO ()
main = runAndReport