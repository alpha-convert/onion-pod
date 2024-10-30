{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveLift #-}

module Main where

import Data.Maybe (mapMaybe)
import Test.QuickCheck
import ElimTerm
import Term
import Types
import Events
import Data.Foldable (toList)
import Control.Monad.State as ST
import Control.Monad (when, foldM)
import Data.List (nub, (\\))
import Test.Hspec.QuickCheck
import Test.Hspec
import Data.List (elemIndex)
import PartialOrder as PO
import Data.Set (Set)
import Basic.Sem
import Basic.Stream
import Control.Monad (replicateM)
import Language.Haskell.TH.Syntax
import Basic.Stream ( sFromList, sToList )
import List.Sem
data Binding = Atom String Ty | Pair String Ty String Ty deriving (Eq,Ord,Show,Lift)
data LR = L | R | NA

-- Arguments are always holes.
data PossibleTerm's = HCatR' | HPlusR | HStarR | HStarL | HCatL' | HPlusL | HLet' | HVar'

type Ctx = [Binding]

extractBindings :: Ctx -> [(String, Ty)]
extractBindings = concatMap extractBinding
  where
    extractBinding :: Binding -> [(String, Ty)]
    extractBinding (Atom x ty)      = [(x, ty)]
    extractBinding (Pair x1 ty1 x2 ty2) = [(x1, ty1), (x2, ty2)]

convertTerm :: Term' -> Term
convertTerm EpsR' = EpsR
convertTerm (Var' x s) = Var x s
convertTerm (IntR' n) = IntR n
convertTerm (CatL' x y z e) = CatL x y z (convertTerm e)
convertTerm (CatR' e1 e2) = CatR (convertTerm e1) (convertTerm e2)
convertTerm (InL' e) = InL (convertTerm e)
convertTerm (InR' e) = InR (convertTerm e)
convertTerm (PlusCase' z x e1 y e2) = PlusCase z x (convertTerm e1) y (convertTerm e2)
convertTerm (Nil' _) = Nil
convertTerm (Cons' e1 e2) = Cons (convertTerm e1) (convertTerm e2)
convertTerm (StarCase' z e x xs es) = StarCase z (convertTerm e) x xs (convertTerm es)
convertTerm (Let' x _ e e') = Let x (convertTerm e) (convertTerm e')
convertTerm Rec' = error ""
convertTerm (Fix' e) = Fix (convertTerm e)

data Term' where
    {-
    --------------
    G |- EpsR' : eps
    -}
    EpsR' :: Term'
    {-
    -----------------------
    G;x:s;G' |- Var' x s : s
    -}
    Var' :: String -> Ty -> Term'
    {-
    -----------------
    G |- IntR' n : Int
    -}
    IntR' :: Int -> Term'
    {-
    G' |- e1 : s
    y:Int;G' |- e2 : s
    ------------------------------------
    G;x:Int;G' |- IntCase x e1 y e2 : s
    -}

    {-
    G;x:s;y:t;G' |- e : r
    ----------------------------
    G;z:s.t;G' |- CatL' x y z e : r
    -}
    CatL' :: String -> String -> String -> Term' -> Term'
    {-
    G |- e1 : s
    D |- e2 : t
    ----------------------
    G;D |- (e1;e2) : s . t
    -}
    CatR' :: Term' -> Term' -> Term'
    {-
    -}
    InL' :: Term' -> Term'
    InR' :: Term' -> Term'
    --          z,        x,        e1,     y,        e2
    PlusCase' :: String -> String -> Term' -> String -> Term' -> Term'
    Nil' :: Ty -> Term'
    Cons' :: Term' -> Term' -> Term'
    StarCase' :: String -> Term' -> String -> String -> Term' -> Term'
    -- Wait :: String -> Ty -> Term' -> Term'
    {-
        D |- e : s      G;x:s;G' |- e' : r
        ------------------------------------
        G;D;G' |- let x = e in e' : r
    -}
    -- a    x,        e,      e' 
    Let' :: String -> Ty -> Term' -> Term' -> Term'
    Fix' :: Term' -> Term'
    Rec' :: Term'
    deriving (Eq,Ord,Show)

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

lookupByType :: Ctx -> Ty -> Maybe String
lookupByType [] _ = Nothing
lookupByType (Atom var ty : rest) targetTy
  | ty == targetTy = Just var
  | otherwise = lookupByType rest targetTy
lookupByType (Pair var1 ty1 var2 ty2 : rest) targetTy
  | ty1 == targetTy = Just var1
  | ty2 == targetTy = Just var2
  | otherwise = lookupByType rest targetTy

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
leaf :: StateT (Int, Ctx) Gen (Term', Ty)
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
      int <- IntR' <$> ST.lift arbitrary
      return (int, TyInt)
    TyEps -> return (EpsR', TyEps)
    _ -> do
      add (Atom x s)
      return (Var' x s, s)

leftOrRight :: Gen LR
leftOrRight = do
  choice <- elements [L, R]
  return choice

genTerm' :: Maybe Ty -> Gen ((Term', Ty), (Int, Ctx))
genTerm' maybeTy = sized (\n -> runStateT (go maybeTy R n) (0, []))
  where
    lCases :: Ty -> Int -> StateT (Int, Ctx) Gen (Term', Ty)
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
            return (PlusCase' z x e1 y e2, t)
          2 -> do
            lr <- ST.lift $ leftOrRight
            (_, s) <- go (Just r) lr (n `div` 4)
            x <- fresh
            add (Atom x s)
            return (Var' x s, s)
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

            return (StarCase' z e x xs es, r)
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
            return (CatL' x y z e, r)
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
            return (Let' x s e e', r)
          _ -> undefined
    go :: Maybe Ty -> LR -> Int -> StateT (Int, Ctx) Gen (Term', Ty)
    go (Just TyEps) _ _ = return (EpsR', TyEps)
    go (Just TyInt) _ _ = do
      tm <- IntR' <$> ST.lift arbitrary
      return (tm, TyInt)
    go (Just r) L n = lCases r n
    go (Just (TyStar s)) _ 0 = do
      return (Nil' (TyStar s), TyStar s)
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
      return (CatR' e1 e2, TyCat s t)
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
          return (CatR' x y, TyCat s t)
        HCatL' -> do
          (_, s) <- go Nothing NA (n `div` 4)
          (_, t) <- go Nothing NA (n `div` 4)

          x <- fresh
          y <- fresh

          splitAndInsert [Pair x s y t]
          (e, r) <- go Nothing NA (n `div` 4)

          z <- fresh
          replaceElement [Atom z (TyCat s t)] x
          return (CatL' x y z e, r)
      {-
        HStarR -> do
          (gamma, delta) <- split
          replace gamma
          (e, s) <- go Nothing NA (n `div` 4) 
          (_, gamma') <- get
          replace (safeConcat gamma' delta)
          return (Cons' e (Nil' (TyStar s)), TyStar s)
        -}
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

          return (StarCase' z e x xs es, r)
{-
        HPlusR -> do
          (e1, s) <- go Nothing NA (n `div` 4)
          (e2, t) <- go Nothing NA (n `div` 4)
          ST.lift $ oneof [return (InL' e1, TyPlus s t), return (InR' e2, TyPlus s t)]
-}
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
          return (PlusCase' z x e1 y e2, r1)
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

          return (Let' x s e e', t)
        HVar' -> do
          (_, s) <- go Nothing NA (n `div` 4)
          x <- fresh
          add (Atom x s)
          return (Var' x s, s)
    go _ _ _ = undefined

data Error = TypeMismatch
           | OrderViolation (Maybe String) (Maybe String) String
           | NotImplemented Term' 
           | LookupFailed String
           | UnfilledHole
           deriving (Show, Eq)

matchType :: Ty -> (Ty, PO.Pairs) -> Either Error (Ty, PO.Pairs)
matchType expected (actual, order)
    | actual == expected = Right (actual, order)
    | otherwise = Left $ TypeMismatch

orderSequential :: Ty -> PO.Pairs -> PO.Pairs -> Either Error (Ty, PO.Pairs)
orderSequential ty path1 path2 = 
  let path' = PO.concat' path1 path2 in
    case PO.antisymmetric path' of
      Just (a, b) -> Left (OrderViolation (Just a) (Just b) "Sequential")
      Nothing -> Right (ty, path')

orderUnion :: String -> Ty -> PO.Pairs -> PO.Pairs -> Either Error (Ty, PO.Pairs)
orderUnion name ty path1 path2 =
  let path' = PO.union path1 path2 in
    case PO.antisymmetric path' of
      Just (a, b) -> Left (OrderViolation (Just a) (Just b) name)
      Nothing -> Right (ty, path')

check :: Ctx -> Term' -> Ty -> Either Error (Ty, PO.Pairs)
check _ (EpsR') s = matchType s (TyEps, PO.empty)
check _ (IntR' _) s = matchType s (TyInt, PO.empty)
check _ (Nil' t) s = matchType s (t, PO.empty)

check ctx (Var' x s) s' = do
    matchType s' (s, PO.empty) >>= \(_, _) ->
      lookup' ctx x >>= \(s'', po') -> matchType s'' (s, po')

check ctx (Cons' eh et) ss = 
    case ss of
        (TyStar s) -> do
            check ctx eh s >>= \(_, hOrder) ->
                check ctx et (TyStar s) >>= \(_, tOrder) ->
                    orderSequential ss hOrder tOrder
        _ -> Left $ TypeMismatch

check ctx (CatR' e1 e2) st =
    case st of
        (TyCat s t) -> do
            check ctx e1 s >>= \(_, e1Order) ->
                check ctx e2 t >>= \(_, e2Order) ->
                    orderSequential st e1Order e2Order
        _ -> Left $ TypeMismatch

check ctx (CatL' x y z e) st = 
  lookup' ctx z >>= \(zt, zOrder) -> 
      case zt of 
          (TyCat s t) -> do
            let ctx' = replaceElement' ctx z [Pair x s y t]
            check ctx' e st >>= \(_, eOrder) ->
              if not (PO.greaterThan y x eOrder)
                then return (st, eOrder)
                else Left $ OrderViolation (Just x) (Just y) "CatL'"
          _ -> Left $ TypeMismatch

check ctx (InL' e) st =
    case st of 
        (TyPlus s _) -> check ctx e s
        _ -> Left $ TypeMismatch

check ctx (InR' e) st =
    case st of 
        (TyPlus _ t) -> check ctx e t
        _ -> Left $ TypeMismatch

check ctx (PlusCase' z x e1 y e2) r =
    lookup' ctx z >>= \(zt, zOrder) -> 
      case zt of
        (TyPlus s t) -> do
            let ctx' = replaceElement' ctx z [Atom x s]
            check ctx' e1 r >>= \(_, e1Order) -> do
              let ctx'' = replaceElement' ctx' z [Atom y t]
              check ctx'' e2 r >>= \(_, e2Order) ->
                orderUnion "PlusCase'-U" r e1Order e2Order >>= \(_, eOrders) ->
                orderSequential r zOrder eOrders
        _ -> Left $ TypeMismatch

check ctx (StarCase' z e x xs es) r =
  lookup' ctx z >>= \(zt, zOrder) ->
    case zt of
      (TyStar s) -> do
        let ctx' = replaceElement' ctx z []
        check ctx' e r >>= \(_, eOrder) -> do
          let ctx'' = replaceElement' ctx z [Pair x s xs (TyStar s)]
          check ctx'' es r >>= \(_, esOrder) ->
            if not (PO.greaterThan x xs esOrder)
              then
                orderUnion "StarCase'-U" r eOrder esOrder >>= \(_, combinedOrder) ->
                  orderSequential r zOrder combinedOrder
              else
                Left $ OrderViolation (Just x) (Just xs) "StarCase'"
      _ -> Left $ TypeMismatch

check ctx (Let' x s e e') r = do
    check ctx e s >>= \(_, eUses) ->
      check (safeConcat ctx [(Atom x s)]) e' r >>= \(e't, e'Uses) ->
        let all_e_vars = concatMap (\(a, b) -> [a, b]) (PO.toList eUses) in
        orderUnion "Let'-U" e't eUses (PO.substAll all_e_vars x e'Uses)

check _ term _ = Left $ NotImplemented term

-- Generate a sequence of TaggedEvents from a given context
generateTaggedEvents :: Ctx -> Gen [TaggedEvent]
generateTaggedEvents ctx = do
    let bindings = extractBindings ctx  -- Extract the (String, Ty) pairs from the context
    genTaggedEventsForContext bindings  -- Generate the TaggedEvents for the bindings

semElimTerm' :: ElimTerm -> Stream TaggedEvent -> Stream Event
semElimTerm' a (S sf) = S (semElimTerm a sf)

exactSemSpec :: String -> Ctx -> Term -> SpecWith ()
exactSemSpec s ctx tm = it s $ do
    -- Generate tagged events from the given context
    taggedEvents <- generate $ generateTaggedEvents ctx
    
    -- Print the generated tagged events for inspection
    putStrLn $ "Generated Tagged Events: " ++ show taggedEvents
    
    -- Convert the term to its elimination form
    let eltm = inlineElims tm
    
    -- Evaluate the term using the elimination semantics
    let evaluatedEvents = sToList (semElimTerm' eltm (sFromList taggedEvents))
    
    -- Compute the expected events using the List.Sem semantics
    let expectedEvents = List.Sem.bigStepTerm tm taggedEvents
    
    -- Print both the evaluated and expected events for comparison
    putStrLn $ "Evaluated Events: " ++ show evaluatedEvents
    putStrLn $ "Expected Events: " ++ show expectedEvents
    
    -- Perform the actual comparison between evaluated and expected events
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
categorizeError UnfilledHole counts = counts { hole = hole counts + 1 }

initialErrorCount :: ErrorCount
initialErrorCount = ErrorCount 0 0 0 0 0

prop_check_term :: Gen (Either (Error, Term', Ty, Ty, Ctx) (PO.Pairs, Term', Ty, Ty, Ctx))
prop_check_term = do
  ((term, inferredTy), (_, ctx)) <- genTerm' Nothing
  return $ case check ctx term inferredTy of
    Right (ty', pairs) -> Right (pairs, term, TyEps, inferredTy, ctx)
    Left err           -> Left (err, term, TyEps, inferredTy, ctx)

runAndReport :: IO ()
runAndReport = do
  results <- generate (replicateM 100000 prop_check_term)

  -- Use foldM instead of foldl to handle IO in the accumulator
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
  putStrLn $ "Hole Errors: " ++ show (hole errorCounts)

categorizeResult :: (Int, ErrorCount, [(PO.Pairs, Term', Ty, Ty, Ctx)], [(Error, Term', Ty, Ty, Ctx)]) 
                 -> Either (Error, Term', Ty, Ty, Ctx) (PO.Pairs, Term', Ty, Ty, Ctx) 
                 -> IO (Int, ErrorCount, [(PO.Pairs, Term', Ty, Ty, Ctx)], [(Error, Term', Ty, Ty, Ctx)])
categorizeResult (successes, counts, successesList, failuresList) (Right (po, term, originalTy, inferredTy, ctx)) = do
  -- Generate semantic evaluation after type checking success
  putStrLn "\nTerm passed type checking:"
  putStrLn $ "Term': " ++ show term
  putStrLn $ "Inferred Type: " ++ show inferredTy
  putStrLn $ "Context: " ++ show ctx

  -- Run the semantic evaluation inline (replacing exactSemSpec)
  let termConv = convertTerm term  -- Convert Term' to Term for semantic evaluation
  let taggedEventsGen = generateTaggedEvents ctx  -- Generate TaggedEvents based on the context
  taggedEvents <- generate taggedEventsGen  -- Actually generate the events

  -- Print the generated TaggedEvents for inspection
  putStrLn $ "Generated Tagged Events: " ++ show taggedEvents

  -- Inline elimination and semantic evaluation
  let eltm = inlineElims termConv
  let evaluatedEvents = sToList (semElimTerm' eltm (sFromList taggedEvents))
  let expectedEvents = List.Sem.bigStepTerm termConv taggedEvents

  -- Print the evaluated and expected events for comparison
  putStrLn $ "Evaluated Events: " ++ show evaluatedEvents
  putStrLn $ "Expected Events: " ++ show expectedEvents

  return (successes + 1, counts, (po, term, originalTy, inferredTy, ctx) : successesList, failuresList)

categorizeResult (successes, counts, successesList, failuresList) (Left (err, term, originalTy, inferredTy, ctx)) = do
  -- Print the error for failed terms
  putStrLn "----------------------------"
  putStrLn $ "Generated Term': " ++ show term
  putStrLn $ "Inferred Type: " ++ show inferredTy
  putStrLn $ "Context: " ++ show ctx
  putStrLn $ "Error: " ++ show err

  return (successes, categorizeError err counts, successesList, (err, term, originalTy, inferredTy, ctx) : failuresList)

main :: IO ()
main = runAndReport