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
    Nil :: Ty -> Term
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

replace :: Ctx -> StateT (Int, Ctx, PO.Pairs) Gen ()
replace ctx' = do
  (n, _, pairs) <- get
  put (n, ctx', pairs)

replaceElement' :: Ctx -> String -> Ctx -> Ctx
replaceElement' ctx x ctx' =
  let (ctx0, rest) = break (matches x) ctx
      ctx1 = case rest of
               [] -> []              
               (_ : rest') -> rest'
  in ctx0 ++ ctx' ++ ctx1

-- Helper function to check if a binding matches the variable `x`
matches :: String -> Binding -> Bool
matches x (Atom var _) = var == x
matches x (Pair var1 _ var2 _) = var1 == x || var2 == x

lookup' :: Ctx -> String -> Maybe Ty
lookup' [] _ = Nothing
lookup' (Atom k v : rest) x
    | k == x = Just v
    | otherwise = lookup' rest x
lookup' (Pair k1 v1 k2 v2 : rest) x
    | k1 == x = Just v1
    | k2 == x = Just v2
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

lookupOrBind :: Ty -> StateT (Int, Ctx) Gen String
lookupOrBind s = do
  (_, ctx) <- get
  case lookupByType ctx s of
    Just x -> return x
    Nothing -> do
      x <- binding s
      return x

binding :: Ty -> StateT (Int, Ctx) Gen String
binding s = do
  x <- fresh
  add (Atom x s)
  return x

add :: Binding -> StateT (Int, Ctx) Gen ()
add el = do
  (n, ctx) <- get
  put (n, safeConcat ctx [el])

genTm :: Ty -> Gen (Term, (Int, Ctx))
genTm t = sized (\n -> runStateT (go t n) (0, []))
    where 
        go :: Ty -> Int -> StateT (Int, Ctx) Gen Term
        go TyEps _ = return EpsR
        go TyInt _ = IntR <$> lift arbitrary
        go (TyPlus s t) 0 = undefined
        go _ _ = undefined

data Error = TypeMismatch Ty Ty 
           | OrderViolation 
           | NotImplemented Term 
           | LookupFailed String
           deriving (Show, Eq)

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
check _ (Nil t) s = matchType s (t, PO.empty)

check ctx (Var x s) s' = do
    matchType s' (s, PO.empty) >>= \(_, po) ->
        case lookup' ctx x of
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
    case lookup' ctx z of
        Just (TyCat s t) -> do
            let ctx' = replaceElement' ctx z [Pair x s y t]
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
    case lookup' ctx z of
        Just (TyPlus s t) -> do
            let ctx' = replaceElement' ctx z [Atom x s]
            check ctx' e1 r >>= \(_, e1Order) -> do
                let ctx'' = replaceElement' ctx z [Atom y t]
                check ctx'' e2 r >>= \(_, e2Order) ->
                    imposeUnionOrder r e1Order e2Order
        _ -> Left $ LookupFailed z

check ctx (StarCase z e x xs es) r =
    case lookup' ctx z of
        Just (TyStar s) -> do
            let ctx' = replaceElement' ctx z []
            check ctx' e s >>= \(_, eOrder) -> do
                let ctx'' = replaceElement' ctx z [Pair x s xs (TyStar s)]
                check ctx'' es (TyStar s) >>= \(_, esOrder) ->
                    if PO.lessThan x xs esOrder
                        then imposeUnionOrder r eOrder esOrder
                        else Left OrderViolation
        _ -> Left $ LookupFailed z

check ctx (Let x s e e') r = do
    (_, eUses) <- check ctx e s
    (e't, e'Uses) <- check (safeConcat ctx [(Atom x s)]) e' r
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
  (term, (_, ctx)) <- genTm ty
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
  putStrLn $ "Success rate: " ++ show (fromIntegral successes / 100 * 100) ++ "%"
  putStrLn $ "Failure rate: " ++ show (fromIntegral numFailed / 100 * 100) ++ "%"

  putStrLn "\nError breakdown:"
  putStrLn $ "Order Violations: " ++ show (orderViolations errorCounts)
  putStrLn $ "Type Mismatches: " ++ show (typeMismatches errorCounts)
  putStrLn $ "Lookup Failures: " ++ show (lookupFailures errorCounts)
  putStrLn $ "Not Implemented Errors: " ++ show (notImplemented errorCounts)

categorizeResult :: (Int, ErrorCount) -> Either Error () -> (Int, ErrorCount)
categorizeResult (successes, counts) (Right _) = (successes + 1, counts)  -- Success
categorizeResult (successes, counts) (Left err) = (successes, categorizeError err counts)  -- Failure with error

main :: IO ()
main = runAndReport