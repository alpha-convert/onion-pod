{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveLift #-}

module Main where

import Data.Maybe (mapMaybe)
import Test.QuickCheck
import ElimTerm
import Events
import Data.Foldable (toList)
import Control.Monad.State as ST
import Control.Monad (when)
import Data.List (nub, (\\))
import Test.Hspec.QuickCheck
import Test.Hspec
import Data.List (elemIndex)
import PartialOrder as PO
import Data.Set (Set)
import Control.Monad (replicateM)
import Language.Haskell.TH.Syntax

data Binding = Atom String Ty | Pair String Ty String Ty
data Ty = TyEps | TyInt | TyCat Ty Ty | TyPlus Ty Ty | TyStar Ty | Hole deriving (Eq,Ord,Show,Lift)
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

-- Top-level is always not a hole.
genTy :: Gen Ty
genTy = sized go
  where
    go 0 = frequency [(1, return TyEps), (1, return TyInt)] --, (1, return Hole)]
    go n = frequency [ (2, TyCat <$> go (n `div` 2) <*> go (n `div` 2))
                     , (2, TyPlus <$> go (n `div` 2) <*> go (n `div` 2))
                     , (2, TyStar <$> go (n `div` 2))
                     , (1, return TyEps)
                     , (1, return TyInt)]

genTyConcrete :: Gen Ty
genTyConcrete = sized go
  where
    go 0 = frequency [(1, return TyEps), (1, return TyInt)]
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
  n <- ST.lift $ choose (0, length ctx)
  let ctx0 = take n ctx
  let ctx1 = drop n ctx
  return (ctx0, ctx1)

splitAndInsert :: Ctx -> StateT (Int, Ctx) Gen ()
splitAndInsert ctx = do
  (ctx0, ctx1) <- split
  replace $ safeConcat (safeConcat ctx0 ctx) ctx1

genTm :: Ty -> Gen ((Term, Ty), (Int, Ctx))
genTm ty = sized (\n -> runStateT (go ty n) (0, []))
    where 
      go :: Ty -> Int -> StateT (Int, Ctx) Gen (Term, Ty)
      go TyEps _ = return (EpsR, TyEps)
      go TyInt _ = do
        tm <- IntR <$> ST.lift arbitrary
        return (tm, TyInt)
      go (TyPlus s t) 0 = do  
        x <- lookupOrBind (TyPlus s t)
        return (Var x (TyPlus s t), TyPlus s t)
      go (TyPlus s t) n = do
        (l, _) <- go s (n `div` 2)
        (r, _) <- go t (n `div` 2)
        (other, _) <- go' (TyPlus s t) n
        choice <- ST.lift $ oneof [return (InL l), return (InR r), return other]
        return (choice, TyPlus s t)
      go (TyCat s t) 0 = do
        x <- lookupOrBind (TyCat s t)
        return (Var x (TyCat s t), TyCat s t)
      go (TyCat s t) n = do
        (gamma, delta) <- split
        replace gamma
        (e1, _) <- go s (n `div` 2)
        (_, gamma') <- get
        replace delta
        (e2, _) <- go t (n `div` 2)
        (_, delta') <- get
        replace (safeConcat gamma' delta')
        let catr = CatR e1 e2
        (other, _) <- go' (TyCat s t) n
        choice <- ST.lift $ oneof [return catr, return other]
        return (choice, TyCat s t)
      go (TyStar s) 0 = return (Nil (TyStar s), TyStar s)
      go (TyStar s) n = do
        let nil = Nil (TyStar s)
        (gamma, delta) <- split
        replace gamma
        (e1, _) <- go s (n `div` 2)
        (_, gamma') <- get
        replace delta
        (e2, _) <- go (TyStar s) (n `div` 2)
        (_, delta') <- get
        replace (gamma' ++ delta')
        let lst = Cons e1 e2
        (other, _) <- go' (TyStar s) n
        choice <- ST.lift $ oneof [return nil, return lst, return other]
        return (choice, TyStar s)
      go Hole _ = do
        (_, ctx) <- get
        let ctxList = extractBindings ctx
        if null(ctxList)
          then do
            x <- fresh
            s <- ST.lift genTyConcrete
            add (Atom x s)
            return $ (Var x s, s)
          else do
            n <- ST.lift $ choose (0, length ctxList - 1)  -- Choose a valid index
            let (x, s) = ctxList !! n
            return (Var x s, s)
      go' :: Ty -> Int -> StateT (Int, Ctx) Gen (Term, Ty)
      go' r 0 = do
        (_, ctx) <- get
        let x = lookupByType ctx r
        case x of
          Just x -> return (Var x r, r)
          Nothing -> go r 1
      go' r n = do
        choice <- ST.lift $ elements [1..4]
        case choice of
          1 -> do
              x <- fresh
              s <- ST.lift genTyConcrete
              t <- ST.lift genTyConcrete

              splitAndInsert [Atom x s]
              (e1, _) <- go r (n `div` 2)
            
              y <- fresh
              replaceElement [Atom y t] x
            
              (e2, _) <- go r (n `div` 2)
            
              z <- fresh
              replaceElement [Atom z (TyPlus s t)] y
              return (PlusCase z x e1 y e2, r)
          2 -> do                  
              x <- fresh
              s <- ST.lift genTyConcrete

              (gamma', temp) <- split
              replace temp
              (delta, gamma'') <- split
              replace (safeConcat (safeConcat gamma' [Atom x s]) gamma'')

              (e', _) <- go r (n `div` 2)
              (_, ctx') <- get

              replace delta

              (e, _) <- go s (n `div` 2)
              (_, delta') <- get

              replace ctx'
              replaceElement delta' x

              return (Let x s e e', r)
          3 -> do                                             
              z <- fresh
              s <- ST.lift genTyConcrete
              t <- ST.lift genTyConcrete
              x <- fresh
              y <- fresh

              splitAndInsert [Pair x s y t]

              (e, _) <- go r (n `div` 2)

              replaceElement [Atom z (TyCat s t)] x

              return (CatL x y z e, r)
          4 -> do                                           
              z <- fresh
              s <- ST.lift genTyConcrete

              (e, _) <- go s (n `div` 2)

              splitAndInsert [Atom z (TyStar s)]

              x <- fresh
              xs <- fresh

              replaceElement [Pair x s xs (TyStar s)] z

              (es, _) <- go (TyStar s) (n `div` 2)

              replaceElement [Atom z (TyStar s)] x

              return (StarCase z e x xs es, r)
          _ -> error "Shouldn't be possible..."

data Error = TypeMismatch
           | OrderViolation 
           | NotImplemented Term 
           | LookupFailed String
           | UnfilledHole
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

checkForHoles :: Ty -> Either Error ()
checkForHoles Hole = Left $ UnfilledHole
checkForHoles (TyCat s t) = checkForHoles s >> checkForHoles t
checkForHoles (TyPlus s t) = checkForHoles s >> checkForHoles t
checkForHoles (TyStar s) = checkForHoles s
checkForHoles _ = return ()

check :: Ctx -> Term -> Ty -> Either Error (Ty, PO.Pairs)
check _ _ Hole = Left $ UnfilledHole
check _ (EpsR) s = checkForHoles s >> matchType s (TyEps, PO.empty)
check _ (IntR _) s = checkForHoles s >> matchType s (TyInt, PO.empty)
check _ (Nil t) s = checkForHoles s >> matchType s (t, PO.empty)

check ctx (Var x s) s' = do
    checkForHoles s
    checkForHoles s'
    matchType s' (s, PO.empty) >>= \(_, _) ->
      lookup' ctx x >>= \(s'', po') -> matchType s'' (s, po')

check ctx (Cons eh et) ss = 
    checkForHoles ss >>
    case ss of
        (TyStar s) -> do
            check ctx eh s >>= \(_, hOrder) ->
                check ctx et (TyStar s) >>= \(_, tOrder) ->
                    orderSequential ss hOrder tOrder
        _ -> Left $ TypeMismatch

check ctx (CatR e1 e2) st =
    checkForHoles st >>
    case st of
        (TyCat s t) -> do
            check ctx e1 s >>= \(_, e1Order) ->
                check ctx e2 t >>= \(_, e2Order) ->
                    orderSequential st e1Order e2Order
        _ -> Left $ TypeMismatch

check ctx (CatL x y z e) st = 
  checkForHoles st >>
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
    checkForHoles st >>
    case st of 
        (TyPlus s _) -> check ctx e s
        _ -> Left $ TypeMismatch

check ctx (InR e) st =
    checkForHoles st >>
    case st of 
        (TyPlus _ t) -> check ctx e t
        _ -> Left $ TypeMismatch

check ctx (PlusCase z x e1 y e2) r =
    checkForHoles r >>
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
  checkForHoles r >>
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
    checkForHoles r
    checkForHoles s
    (_, eUses) <- check ctx e s
    (e't, e'Uses) <- check (safeConcat ctx [(Atom x s)]) e' r
    let all_e_vars = PO.toList eUses >>= \(a, b) -> [a, b]
    orderUnion e't eUses (PO.substAll all_e_vars x e'Uses)

check _ term _ = Left $ NotImplemented term

data ErrorCount = ErrorCount {
    orderViolations   :: Int,
    typeMismatches    :: Int,
    lookupFailures    :: Int,
    notImplemented    :: Int,
    hole              :: Int
} deriving (Show)

categorizeError :: Error -> ErrorCount -> ErrorCount
categorizeError (TypeMismatch) counts = counts { typeMismatches = typeMismatches counts + 1 }
categorizeError OrderViolation counts     = counts { orderViolations = orderViolations counts + 1 }
categorizeError (LookupFailed _) counts   = counts { lookupFailures = lookupFailures counts + 1 }
categorizeError (NotImplemented _) counts = counts { notImplemented = notImplemented counts + 1 }
categorizeError UnfilledHole counts = counts { hole = hole counts + 1 }

initialErrorCount :: ErrorCount
initialErrorCount = ErrorCount 0 0 0 0 0

prop_check_term :: Gen (Either (Error, Term, Ty, Ty) (PO.Pairs, Term, Ty, Ty))
prop_check_term = do
  originalTy <- genTy
  ((term, inferredTy), (_, ctx)) <- genTm originalTy
  return $ case check ctx term inferredTy of
    Right (ty', pairs) -> Right (pairs, term, originalTy, inferredTy)
    Left err           -> Left (err, term, originalTy, inferredTy)

runAndReport :: IO ()
runAndReport = do
  results <- generate (replicateM 1000 prop_check_term)

  let (successes, errorCounts, successesList, failuresList) = 
        foldl categorizeResult (0, initialErrorCount, [], []) results

  let numFailed = 1000 - successes

  putStrLn "\nGenerated Terms and Their Types (Successful Checks):"
  mapM_ printTermAndTypes successesList

  putStrLn "\nFailed Terms and Their Errors:"
  mapM_ printFailedTermAndError failuresList

  putStrLn $ "\nTotal terms generated: " ++ show 1000
  putStrLn $ "Successful type checks: " ++ show successes
  putStrLn $ "Failed type checks: " ++ show numFailed
  putStrLn $ "Success rate: " ++ show (fromIntegral successes / 1000 * 100) ++ "%"
  putStrLn $ "Failure rate: " ++ show (fromIntegral numFailed / 1000 * 100) ++ "%"

  putStrLn "\nError breakdown:"
  putStrLn $ "Order Violations: " ++ show (orderViolations errorCounts)
  putStrLn $ "Type Mismatches: " ++ show (typeMismatches errorCounts)
  putStrLn $ "Lookup Failures: " ++ show (lookupFailures errorCounts)
  putStrLn $ "Not Implemented Errors: " ++ show (notImplemented errorCounts)
  putStrLn $ "Hole Errors: " ++ show (hole errorCounts)

printTermAndTypes :: (PO.Pairs, Term, Ty, Ty) -> IO ()
printTermAndTypes (po, term, originalTy, inferredTy) = do
  putStrLn "----------------------------"
  putStrLn $ "Original Type (with holes): " ++ show originalTy
  putStrLn $ "Generated Term: " ++ show term
  putStrLn $ "Inferred Type: " ++ show inferredTy
  putStrLn "Partial Order: "
  print po

printFailedTermAndError :: (Error, Term, Ty, Ty) -> IO ()
printFailedTermAndError (err, term, originalTy, inferredTy) = do
  putStrLn "----------------------------"
  putStrLn $ "Original Type (with holes): " ++ show originalTy
  putStrLn $ "Generated Term: " ++ show term
  putStrLn $ "Inferred Type: " ++ show inferredTy
  putStrLn $ "Error: " ++ show err

categorizeResult :: (Int, ErrorCount, [(PO.Pairs, Term, Ty, Ty)], [(Error, Term, Ty, Ty)]) 
                 -> Either (Error, Term, Ty, Ty) (PO.Pairs, Term, Ty, Ty) 
                 -> (Int, ErrorCount, [(PO.Pairs, Term, Ty, Ty)], [(Error, Term, Ty, Ty)])
categorizeResult (successes, counts, successesList, failuresList) (Right (po, term, originalTy, inferredTy)) =
  (successes + 1, counts, (po, term, originalTy, inferredTy) : successesList, failuresList)
categorizeResult (successes, counts, successesList, failuresList) (Left (err, term, originalTy, inferredTy)) =
  (successes, categorizeError err counts, successesList, (err, term, originalTy, inferredTy) : failuresList)

main :: IO ()
main = runAndReport