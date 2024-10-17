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

lookupOrBind :: Ty -> StateT (Int, Ctx) Gen String
lookupOrBind s = do
  (_, ctx) <- get
  case lookupByType ctx s of
    Just x -> return x
    Nothing -> do
      x <- bind s
      return x

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
  n <- lift $ choose (0, length ctx)
  let ctx0 = take n ctx
  let ctx1 = drop n ctx
  return (ctx0, ctx1)

splitAndInsert :: Ctx -> StateT (Int, Ctx) Gen ()
splitAndInsert ctx = do
  (ctx0, ctx1) <- split
  replace $ safeConcat (safeConcat ctx0 ctx) ctx1

genTm :: Ty -> Gen (Term, (Int, Ctx))
genTm ty = sized (\n -> runStateT (go ty n) (0, []))
    where 
      go :: Ty -> Int -> StateT (Int, Ctx) Gen Term
      go TyEps _ = return EpsR
      go TyInt _ = IntR <$> lift arbitrary
      go (TyPlus s t) 0 = do  
        x <- lookupOrBind (TyPlus s t)
        return $ Var x (TyPlus s t)
      go (TyPlus s t) n = do
        l <- InL <$> go s (n `div` 2)
        r <- InR <$> go t (n `div` 2)
        other <- go' (TyPlus s t) n
        lift $ oneof [return l, return r, return other]
      go (TyCat s t) 0 = do
        x <- lookupOrBind (TyCat s t)
        return $ Var x (TyCat s t)
      go (TyCat s t) n = do
        catr <- do
          (gamma, delta) <- split
          replace gamma
          e1 <- go s (n `div` 2)
          (_, gamma') <- get
          replace delta
          e2 <- go t (n `div` 2)
          (_, delta') <- get
          replace (safeConcat gamma' delta')
          return $ CatR e1 e2
        other <- go' (TyCat s t) n
        lift $ oneof [return catr, return other]
      go (TyStar s) 0 = return $ Nil (TyStar s)
      go (TyStar s) n = do
        nil <- return $ Nil (TyStar s)
        lst <- do                                                                    
            (gamma, delta) <- split
            replace gamma
            e1 <- go s (n `div` 2)
            (_, gamma') <- get
            replace delta
            e2 <- go (TyStar s) (n `div` 2)
            (_, delta') <- get
            replace (gamma' ++ delta')
            return $ Cons e1 e2
        other <- go' (TyStar s) n
        lift $ oneof [return nil, return lst, return other]
      go' :: Ty -> Int -> StateT (Int, Ctx) Gen Term
      go' r 0 = do
        x <- lookupOrBind r
        return $ Var x r
      go' r n = do
        choice <- lift $ elements [0..4]
        case choice of
          0 -> do                                              
              x <- lookupOrBind r
              return $ Var x r
          1 -> do
              x <- fresh
              s <- lift genTy
              t <- lift genTy 

              splitAndInsert [Atom x s]
            
              e1 <- go r (n `div` 2)
            
              y <- fresh
              replaceElement [Atom y t] x
            
              e2 <- go r (n `div` 2)
            
              z <- fresh
              replaceElement [Atom z (TyPlus s t)] y
              return $ PlusCase z x e1 y e2
          2 -> do                  
              x <- fresh
              s <- lift genTy

              (gamma', temp) <- split
              replace temp
              (delta, gamma'') <- split
              replace (safeConcat (safeConcat gamma' [Atom x s]) gamma'')

              e' <- go r (n `div` 2)
              (_, ctx') <- get

              replace delta

              e <- go s (n `div` 2)
              (_, delta') <- get

              replace ctx'
              replaceElement delta' x

              return $ Let x s e e'
          3 -> do                                             
              z <- fresh
              s <- lift genTy
              t <- lift genTy
              x <- fresh
              y <- fresh

              splitAndInsert [Pair x s y t]

              e <- go r (n `div` 2)

              replaceElement [Atom z (TyCat s t)] x

              return $ CatL x y z e
          4 -> do                                           
              z <- fresh
              s <- lift genTy

              e <- go s (n `div` 2)

              splitAndInsert [Atom z (TyStar s)]

              x <- fresh
              xs <- fresh

              replaceElement [Pair x s xs (TyStar s)] z

              es <- go (TyStar s) (n `div` 2)

              replaceElement [Atom z (TyStar s)] x

              return $ StarCase z e x xs es
          _ -> error "Shouldn't be possible..."

data Error = TypeMismatch
           | OrderViolation 
           | NotImplemented Term 
           | LookupFailed String
           deriving (Show, Eq)

matchType :: Ty -> (Ty, PO.Pairs) -> Either Error (Ty, PO.Pairs)
matchType expected (actual, order)
    | actual == expected = Right (actual, order)
    | otherwise = Left $ TypeMismatch

orderSequential :: Ty -> PO.Pairs -> PO.Pairs -> Either Error (Ty, PO.Pairs)
orderSequential ty path1 path2 = 
  let path' = PO.concat' path1 path2
  in case PO.antisymmetric path' of
       Just _ -> Left OrderViolation
       Nothing -> Right (ty, path') 

orderUnion :: Ty -> PO.Pairs -> PO.Pairs -> Either Error (Ty, PO.Pairs)
orderUnion ty path1 path2 =
  let path' = PO.union path1 path2
  in case PO.antisymmetric path' of
       Just _ -> Left OrderViolation
       Nothing -> Right (ty, path')

check :: Ctx -> Term -> Ty -> Either Error (Ty, PO.Pairs)
check _ (EpsR) s = matchType s (TyEps, PO.empty)
check _ (IntR _) s = matchType s (TyInt, PO.empty)
check _ (Nil t) s = matchType s (t, PO.empty)

check ctx (Var x s) s' = do
    matchType s' (s, PO.empty) >>= \(_, _) ->
      lookup' ctx x >>= \(s'', po') -> matchType s'' (s, po')

check ctx (Cons eh et) ss = 
    case ss of
        (TyStar s) -> do
            check ctx eh s >>= \(_, hOrder) ->
                check ctx et (TyStar s) >>= \(_, tOrder) ->
                    orderSequential ss hOrder tOrder
        _ -> Left $ TypeMismatch

check ctx (CatR e1 e2) st =
    case st of
        (TyCat s t) -> do
            check ctx e1 s >>= \(_, e1Order) ->
                check ctx e2 t >>= \(_, e2Order) ->
                    orderSequential st e1Order e2Order
        _ -> Left $ TypeMismatch

check ctx (CatL x y z e) st = 
  lookup' ctx z >>= \(zt, zOrder) -> 
      case zt of 
          (TyCat s t) -> do
            let ctx' = replaceElement' ctx z [Pair x s y t]
            check ctx' e st >>= \(_, eOrder) ->
              if not (PO.greaterThan y x eOrder)
                then return (st, insert (x, y) eOrder) -- Not really necessary?
                else Left $ OrderViolation
          _ -> Left $ TypeMismatch

check ctx (InL e) st =
    case st of 
        (TyPlus s _) -> check ctx e s
        _ -> Left $ TypeMismatch

check ctx (InR e) st =
    case st of 
        (TyPlus _ t) -> check ctx e t
        _ -> Left $ TypeMismatch

check ctx (PlusCase z x e1 y e2) r =
    lookup' ctx z >>= \(zt, zOrder) -> 
      case zt of
        (TyPlus s t) -> do
            let ctx' = replaceElement' ctx z [Atom x s]
            check ctx' e1 r >>= \(_, e1Order) -> do
              let ctx'' = replaceElement' ctx' z [Atom y t]
              check ctx'' e2 r >>= \(_, e2Order) ->
                orderUnion r e1Order e2Order >>= \(_, eOrders) ->
                orderSequential r zOrder eOrders
        _ -> Left $ TypeMismatch

check ctx (StarCase z e x xs es) r =
  lookup' ctx z >>= \(zt, zOrder) ->
    case zt of
      (TyStar s) -> do
        let ctx' = replaceElement' ctx z []
        check ctx' e s >>= \(_, eOrder) -> do
          let ctx'' = replaceElement' ctx z [Pair x s xs (TyStar s)]
          check ctx'' es (TyStar s) >>= \(_, esOrder) ->
            if not (PO.greaterThan x xs esOrder)
              then
                orderUnion r eOrder (insert (x, xs) esOrder) >>= \(_, combinedOrder) ->
                  orderSequential r zOrder combinedOrder
              else
                Left $ OrderViolation
      _ -> Left $ TypeMismatch

check ctx (Let x s e e') r = do
    (_, eUses) <- check ctx e s
    (e't, e'Uses) <- check (safeConcat ctx [(Atom x s)]) e' r
    let all_e_vars = PO.toList eUses >>= \(a, b) -> [a, b]
    orderUnion e't eUses (PO.substAll all_e_vars x e'Uses)

check _ term _ = Left $ NotImplemented term

data ErrorCount = ErrorCount {
    orderViolations   :: Int,
    typeMismatches    :: Int,
    lookupFailures    :: Int,
    notImplemented    :: Int
} deriving (Show)

categorizeError :: Error -> ErrorCount -> ErrorCount
categorizeError (TypeMismatch) counts = counts { typeMismatches = typeMismatches counts + 1 }
categorizeError OrderViolation counts     = counts { orderViolations = orderViolations counts + 1 }
categorizeError (LookupFailed _) counts   = counts { lookupFailures = lookupFailures counts + 1 }
categorizeError (NotImplemented _) counts = counts { notImplemented = notImplemented counts + 1 }

initialErrorCount :: ErrorCount
initialErrorCount = ErrorCount 0 0 0 0

prop_check_term :: Gen (Either Error (PO.Pairs, (Ty, PO.Pairs)))
prop_check_term = do
  ty <- genTy
  (term, (_, ctx)) <- genTm ty
  return $ case check ctx term ty of
    Right (ty, pairs) -> Right (pairs, (ty, pairs))
    Left err     -> Left err

runAndReport :: IO ()
runAndReport = do
  results <- generate (replicateM 1000 prop_check_term)

  let (successes, errorCounts, orders) = foldl categorizeResult (0, initialErrorCount, []) results

  let numFailed = 1000 - successes

  putStrLn "\nPartial Orders from Successful Type Checks:"
  mapM_ (putStrLn . show) orders

  putStrLn $ "Total terms generated: " ++ show 1000
  putStrLn $ "Successful type checks: " ++ show successes
  putStrLn $ "Failed type checks: " ++ show numFailed
  putStrLn $ "Success rate: " ++ show (fromIntegral successes / 1000 * 100) ++ "%"
  putStrLn $ "Failure rate: " ++ show (fromIntegral numFailed / 1000 * 100) ++ "%"

  putStrLn "\nError breakdown:"
  putStrLn $ "Order Violations: " ++ show (orderViolations errorCounts)
  putStrLn $ "Type Mismatches: " ++ show (typeMismatches errorCounts)
  putStrLn $ "Lookup Failures: " ++ show (lookupFailures errorCounts)
  putStrLn $ "Not Implemented Errors: " ++ show (notImplemented errorCounts)

categorizeResult :: (Int, ErrorCount, [PO.Pairs]) -> Either Error (PO.Pairs, (Ty, PO.Pairs)) -> (Int, ErrorCount, [PO.Pairs])
categorizeResult (successes, counts, orders) (Right (po, _)) =
  (successes + 1, counts, po : orders)
categorizeResult (successes, counts, orders) (Left err) =
  (successes, categorizeError err counts, orders)

main :: IO ()
main = runAndReport