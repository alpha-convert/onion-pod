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
import Data.List (elemIndex)
import PartialOrder as PO
import Data.Set (Set)
import Control.Monad (replicateM)

-- type Ctx = [(String, Ty)]

data Binding = Atom String Ty | Pair String Ty String Ty
type Ctx = [Binding]

extractBindings :: Ctx -> [(String, Ty)]
extractBindings = concatMap extractBinding
  where
    extractBinding :: Binding -> [(String, Ty)]
    extractBinding (Atom x ty)      = [(x, ty)]
    extractBinding (Pair x1 ty1 x2 ty2) = [(x1, ty1), (x2, ty2)]

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
    Let :: String -> Ty -> Term -> Term -> Term
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
fresh :: StateT (Int, Ctx, PO.Pairs) Gen String
fresh = do
    (n, ctx, pairs) <- get
    let x = "y_" ++ show (n + 1)
    put (n + 1, ctx, pairs)
    return x

-- Add a binding to the context.
add :: Binding -> StateT (Int, Ctx, PO.Pairs) Gen ()
add el = do
  (n, ctx, pairs) <- get
  put (n, safeConcat ctx [el], pairs)

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

{- safeConcat :: Ctx -> Ctx -> Ctx
safeConcat ctx1 ctx2 =
  let duplicates = [x | (x, _) <- ctx1, x `elem` map fst ctx2]
  in if null (duplicates)
     then ctx1 ++ ctx2
     else error $ "Duplicate bindings found: " 
     ++ show duplicates 
-}

-- Replace the context with a new context.
replace :: Ctx -> StateT (Int, Ctx, PO.Pairs) Gen ()
replace ctx' = do
  (n, _, pairs) <- get
  put (n, ctx', pairs)

replaceElement :: String -> Ctx -> StateT (Int, Ctx, PO.Pairs) Gen ()
replaceElement x ctx' = do
  (_, ctx, pairs) <- get

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
binding :: Ty -> StateT (Int, Ctx, PO.Pairs) Gen String
binding s = do
  x <- fresh
  add (x, s)
  return x

lookupOrBind :: Ty -> StateT (Int, Ctx, PO.Pairs) Gen String
lookupOrBind s = do
  (_, ctx, _) <- get
  case lookupByType ctx s of
    Just x -> return x
    Nothing -> do
      x <- binding s
      return x

split :: StateT (Int, Ctx, PO.Pairs) Gen (Ctx, Ctx)
split = do
  (_, ctx, _) <- get
  n <- lift $ choose (0, length ctx)
  
  let ctx0 = take n ctx
  let ctx1 = drop n ctx
  
  return (ctx0, ctx1)

fillHole :: Ctx -> StateT (Int, Ctx, PO.Pairs) Gen Ctx
fillHole ctx = do
  (_, ctx', _) <- get
  n <- lift $ choose (0, length ctx')
  
  let ctx0 = take n ctx'
  let temp = drop n ctx'
  
  n' <- lift $ choose (0, length temp)
  let delta = take n' temp
  let ctx1 = drop n' temp

  let newCtx = safeConcat (safeConcat ctx0 ctx) ctx1
  replace newCtx

  return delta

insertConstraint :: (String, String) -> StateT (Int, Ctx, PO.Pairs) Gen ()
insertConstraint constraint = do
    (counter, ctx, order) <- get
    let order' = PO.insert constraint order
    put (counter, ctx, order')

splitAndInsert :: Ctx -> StateT (Int, Ctx, PO.Pairs) Gen ()
splitAndInsert ctx = do
  (ctx0, ctx1) <- split
  replace $ safeConcat (safeConcat ctx0 ctx) ctx1

choose' :: Monad m => m Bool -> m a -> m a -> m a
choose' bools opt1 opt2 = do
  choice <- bools
  if choice then opt1 else opt2

genTm :: Ty -> Ctx -> Int -> Gen (Term, (Int, Ctx, PO.Pairs))
genTm ty ctx0 counter0 = sized (\n -> runStateT (go ty n) (counter0, ctx0, PO.empty))
  where
    go :: Ty -> Int -> StateT (Int, Ctx, PO.Pairs) Gen Term
                                                                                            -- EpsR
    go TyEps _ = return EpsR
                                                                                            -- IntR
    go TyInt _ = IntR <$> lift arbitrary
    -- Oops, we bottomed out, make something up?
    go (TyPlus s t) 0 = do  
      x <- lookupOrBind (TyPlus s t)
      return $ Var x (TyPlus s t)
    go (TyPlus s t) n = do                                                                  -- PlusR
      choice <- lift $ elements [True, False]
      if choice
        then do
          choice' <- lift $ elements [True, False]
          if choice'
            then InL <$> go s (n `div` 2)  -- InL
            else InR <$> go t (n `div` 2)  -- InR
        else
          go' (TyPlus s t) n
    go (TyCat s t) 0 = do
      x <- lookupOrBind (TyCat s t)
      return $ Var x (TyCat s t)
    go (TyCat s t) n = do                                                                   -- CatR
      choice <- lift $ elements [True, False]
      if choice 
        then do
          (gamma, delta) <- split
          replace gamma
          e1 <- go s (n `div` 2)
          (_, gamma', _) <- get
          replace delta
          e2 <- go t (n `div` 2)
          (_, delta', _) <- get
          replace (safeConcat gamma' delta')
          return $ CatR e1 e2
        else
          go' (TyCat s t) n
    go (TyStar _) 0 = return $ Nil
    go (TyStar s) n = do
      choice <- lift $ elements [True, False]
      if choice
        then do
            choice' <- lift $ elements [True, False]
            if choice'
                then return $ Nil                                                            -- Nil
                else do                                                                      -- Cons
                    (gamma, delta) <- split
                    replace gamma
                    e1 <- go s (n `div` 2)
                    (_, gamma', _) <- get
                    replace delta
                    e2 <- go (TyStar s) (n `div` 2)
                    (_, delta', _) <- get
                    replace (gamma' ++ delta')
                    return $ Cons e1 e2
        else
            go' (TyStar s) n
    go' :: Ty -> Int -> StateT (Int, Ctx, PO.Pairs) Gen Term
    go' r 0 = do
      x <- lookupOrBind r
      return $ Var x r
    go' r n = do
      choice <- lift $ elements [0..4]
      case choice of
        0 -> do                                                                             -- Var
            x <- lookupOrBind r
            return $ Var x r
        1 -> do                                                                             -- PlusCase
            x <- fresh
            s <- lift genTy
            t <- lift genTy 

            splitAndInsert [(x, s)]
            
            e1 <- go r (n `div` 2)
            
            y <- fresh
            replaceElement x [(y, t)]
            
            e2 <- go r (n `div` 2)
            
            z <- fresh
            replaceElement y [(z, TyPlus s t)]
            return $ PlusCase z x e1 y e2
        2 ->  do                                                                            -- CatL Case
            z <- fresh
            s <- lift genTy
            t <- lift genTy
            x <- fresh
            y <- fresh

            splitAndInsert [(x, s), (y, t)]
            insertConstraint (x, y)

            e <- go r (n `div` 2)

            replaceElement x [(z, TyCat s t)]

            return $ CatL x y z e
        3 -> do                                                                             -- StarCase
            z <- fresh
            s <- lift genTy

            -- Generate e in the environment without z.
            e <- go s (n `div` 2)

            -- Add z.
            splitAndInsert [(z, TyStar s)]

            x <- fresh
            xs <- fresh

            -- Put x, xs where z was.
            replaceElement z [(x, s), (xs, TyStar s)]
            insertConstraint (x, xs)

            es <- go (TyStar s) (n `div` 2)

            replaceElement x [(z, TyStar s)]
            replaceElement xs []

            return $ StarCase z e x xs es
        4 -> do                                                                             -- Let
            x <- fresh
            s <- lift genTy

            delta <- fillHole [(x, s)]

            e' <- go r (n `div` 2)
            (_, ctx', _) <- get

            replace delta

            e <- go s (n `div` 2)
            (_, delta', _) <- get

            replace ctx'
            replaceElement x delta'

            return $ Let x s e e'
        _ -> error ""

retryUntilValid :: Gen Term -> Gen Term
retryUntilValid genTerm = do
    term <- genTerm
    -- Check if the term respects variable ordering
    if checkOrder term
        then return term
        else retryUntilValid genTerm

checkOrder :: Term -> Bool
checkOrder (CatL x y _ e) = validOrder x y e
checkOrder (StarCase _ _ x xs e) = validOrder x xs e
checkOrder _ = True

-- Ensure that x comes before y in the term
validOrder :: String -> String -> Term -> Bool
validOrder x y term =
    let vars = collectVars term
    in case (elemIndex x vars, elemIndex y vars) of
        (Just xIdx, Just yIdx) -> xIdx < yIdx
        _ -> True

collectVars :: Term -> [String]
collectVars (EpsR) = []
collectVars (IntR _) = []
collectVars (Var x _) = [x]
collectVars (CatL x y _ e) = [x, y] ++ collectVars e
collectVars (CatR e1 e2) = collectVars e1 ++ collectVars e2
collectVars (Cons e1 e2) = collectVars e1 ++ collectVars e2
collectVars (Nil) = []
collectVars (InL e) = collectVars e
collectVars (InR e) = collectVars e
collectVars (PlusCase _ _ e1 _ e2) = collectVars e1 ++ collectVars e2
collectVars (StarCase _ e x xs es) = [x, xs] ++ collectVars e ++ collectVars es
collectVars (Let x _ e e') = [x] ++ collectVars e ++ collectVars e'
collectVars (Fix _) = error "Not implemented yet."
collectVars (Rec) = error "Not implemented yet."

lookup :: Ctx -> String -> Maybe Ty
lookup [] _ = Nothing
lookup ((k, v) : rest) x
    | k == x = Just v
    | otherwise = Main.lookup rest x

replaceElement' :: Ctx -> String -> Ctx -> Ctx
replaceElement' ctx x ctx' =
  let (ctx0, rest) = break (\(b, _) -> b == x) ctx
      ctx1 = case rest of
               [] -> []              
               (_ : rest') -> rest'
  in ctx0 ++ ctx' ++ ctx1

data Error = TypeMismatch Ty Ty 
           | OrderViolation 
           | NotImplemented Term 
           | LookupFailed String
           deriving (Show, Eq)

getIndices :: Ctx -> [String] -> [Int]
getIndices ctx vars = mapMaybe (`toIndex` ctx) vars

toIndex :: String -> Ctx -> Maybe Int
toIndex x ctx = elemIndex x (map fst ctx)

matchType :: Ty -> (Ty, PO.Pairs) -> Either Error (Ty, PO.Pairs)
matchType expected (actual, order)
    | actual == expected = Right (actual, order)
    | otherwise = Left $ TypeMismatch actual expected

imposeSequentialOrder :: Ty -> PO.Pairs -> PO.Pairs -> Either Error (Ty, PO.Pairs)
imposeSequentialOrder ty path1 path2 = 
  let path' = PO.concat' path1 path2
  in case PO.isAntisymmetric path' of
       Just _ -> Left OrderViolation
       Nothing -> Right (ty, path') 

imposeUnionOrder :: Ty -> PO.Pairs -> PO.Pairs -> Either Error (Ty, PO.Pairs)
imposeUnionOrder ty path1 path2 =
  let path' = PO.union path1 path2
  in case PO.isAntisymmetric path' of
       Just _ -> Left OrderViolation
       Nothing -> Right (ty, path')

check :: Ctx -> Term -> Ty -> Either Error (Ty, PO.Pairs)
check _ (EpsR) s = matchType s (TyEps, PO.empty)
check _ (IntR _) s = matchType s (TyInt, PO.empty)
check _ Nil s = Right (s, PO.empty)

check ctx (Var x s) s' = do
    matchType s' (s, PO.empty) >>= \(_, po) ->
        case Main.lookup ctx x of
            Just s'' -> matchType s'' (s, po)
            Nothing  -> Left $ LookupFailed x

check ctx (Cons eh et) ss = 
    case ss of
        (TyStar s) -> do
            check ctx eh s >>= \(_, hOrder) ->
                check ctx et (TyStar s) >>= \(_, tOrder) ->
                    imposeSequentialOrder ss hOrder tOrder
        _ -> Left $ TypeMismatch ss (TyStar undefined)

check ctx (CatR e1 e2) st =
    case st of
        (TyCat s t) -> do
            check ctx e1 s >>= \(_, e1Order) ->
                check ctx e2 t >>= \(_, e2Order) ->
                    imposeSequentialOrder st e1Order e2Order
        _ -> Left $ TypeMismatch st (TyCat undefined undefined)

check ctx (CatL x y z e) r =
    case Main.lookup ctx z of
        Just (TyCat s t) -> do
            let ctx' = replaceElement' ctx z [(x, s), (y, t)]
            check ctx' e r >>= \(_, eOrder) ->
                if PO.lessThan x y eOrder
                then return (r, eOrder)
                else Left OrderViolation
        _ -> Left $ LookupFailed z

check ctx (InL e) st =
    case st of 
        (TyPlus s _) -> check ctx e s
        _ -> Left $ TypeMismatch st (TyPlus undefined undefined)

check ctx (InR e) st =
    case st of 
        (TyPlus _ t) -> check ctx e t
        _ -> Left $ TypeMismatch st (TyPlus undefined undefined)

check ctx (PlusCase z x e1 y e2) r =
    case Main.lookup ctx z of
        Just (TyPlus s t) -> do
            let ctx' = replaceElement' ctx z [(x, s)]
            check ctx' e1 r >>= \(_, e1Order) -> do
                let ctx'' = replaceElement' ctx z [(y, t)]
                check ctx'' e2 r >>= \(_, e2Order) ->
                    imposeUnionOrder r e1Order e2Order
        _ -> Left $ LookupFailed z

check ctx (StarCase z e x xs es) r =
    case Main.lookup ctx z of
        Just (TyStar s) -> do
            let ctx' = replaceElement' ctx z []
            check ctx' e s >>= \(_, eOrder) -> do
                let ctx'' = replaceElement' ctx z [(x, s), (xs, TyStar s)]
                check ctx'' es (TyStar s) >>= \(_, esOrder) ->
                    if PO.lessThan x xs esOrder
                        then imposeUnionOrder r eOrder esOrder
                        else Left OrderViolation
        _ -> Left $ LookupFailed z

check ctx (Let x s e e') r = do
    (_, eUses) <- check ctx e s
    (e't, e'Uses) <- check (ctx ++ [(x, s)]) e' r
    let all_e_vars = PO.toList eUses >>= \(a, b) -> [a, b]
    imposeUnionOrder e't eUses (PO.substAll all_e_vars x e'Uses)

check _ term _ = Left $ NotImplemented term

data ErrorCount = ErrorCount {
    orderViolations   :: Int,
    typeMismatches    :: Int,
    lookupFailures    :: Int,
    notImplemented    :: Int
} deriving (Show)

categorizeError :: Error -> ErrorCount -> ErrorCount
categorizeError (TypeMismatch _ _) counts = counts { typeMismatches = typeMismatches counts + 1 }
categorizeError OrderViolation counts     = counts { orderViolations = orderViolations counts + 1 }
categorizeError (LookupFailed _) counts   = counts { lookupFailures = lookupFailures counts + 1 }
categorizeError (NotImplemented _) counts = counts { notImplemented = notImplemented counts + 1 }

initialErrorCount :: ErrorCount
initialErrorCount = ErrorCount 0 0 0 0

prop_check_term :: Gen (Either Error ())
prop_check_term = do
  ty <- genTy
  (term, (_, ctx, _)) <- genTm ty [] 0
  return $ case check ctx term ty of
    Right _  -> Right ()
    Left err -> Left err

runAndReport :: IO ()
runAndReport = do
  results <- generate (replicateM 100 prop_check_term)

  let (successes, errorCounts) = foldl categorizeResult (0, initialErrorCount) results

  let numFailed = 100 - successes

  putStrLn $ "Total terms generated: " ++ show 100
  putStrLn $ "Successful type checks: " ++ show successes
  putStrLn $ "Failed type checks: " ++ show numFailed
  putStrLn $ "Success rate: " ++ show (fromIntegral successes / fromIntegral 100 * 100) ++ "%"
  putStrLn $ "Failure rate: " ++ show (fromIntegral numFailed / fromIntegral 100 * 100) ++ "%"

  putStrLn "\nError breakdown:"
  putStrLn $ "Order Violations: " ++ show (orderViolations errorCounts)
  putStrLn $ "Type Mismatches: " ++ show (typeMismatches errorCounts)
  putStrLn $ "Lookup Failures: " ++ show (lookupFailures errorCounts)
  putStrLn $ "Not Implemented Errors: " ++ show (notImplemented errorCounts)

categorizeResult :: (Int, ErrorCount) -> Either Error () -> (Int, ErrorCount)
categorizeResult (successes, counts) (Right _) = (successes + 1, counts)  -- Success
categorizeResult (successes, counts) (Left err) = (successes, categorizeError err counts)  -- Failure with error

-- Main function to run the test
main :: IO ()
main = runAndReport