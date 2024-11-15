{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveLift #-}

module Generate where
import Test.QuickCheck
import ElimTerm
import Term
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
import GHC.Arr (lessSafeIndex)
import Debug.Trace (trace)
import Visualize
import Text.Printf (printf)

import Test.QuickCheck
import qualified Test.Tyche as Tyche
import Term
import Data.List (nub, intersect)
import Test.QuickCheck
import ElimTerm
import Term
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

import Control.Monad.State
import System.IO
import Data.Either (isRight, isLeft)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

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
extractVarsFromTerm (PlusCase x _ e1 _ e2) = nub $ extractVarsFromTerm e1 ++ extractVarsFromTerm e2 ++ [x]
extractVarsFromTerm (Nil _) = []
extractVarsFromTerm (Cons e1 e2) = nub $ extractVarsFromTerm e1 ++ extractVarsFromTerm e2
extractVarsFromTerm (StarCase x e1 _ _ e2) = nub $ extractVarsFromTerm e1 ++ extractVarsFromTerm e2 ++ [x]
extractVarsFromTerm (Let _ _ e1 e2) = nub $ extractVarsFromTerm e1 ++ extractVarsFromTerm e2
extractVarsFromTerm _ = error ""

extractVarsFromCtx :: Ctx -> [String]
extractVarsFromCtx ctx = nub [x | Atom x _ <- ctx] ++ [x1 | Pair x1 _ x2 _ <- ctx] ++ [x2 | Pair x1 _ x2 _ <- ctx]

data Binding = Atom String Ty | Pair String Ty String Ty deriving (Eq,Ord,Show,Lift)
data LR = L | R | NA deriving (Eq, Ord, Show)

data PossibleTerm's = HCatR | HPlusR | HCatL | HPlusL | HLet | HVar | HInt | HEps | HNil | HCons | HStarL

type Ctx = [Binding]

data Error = TypeMismatch
           | OrderViolation (Maybe String) (Maybe String) String
           | NotImplemented Term 
           | LookupFailed String
           deriving (Show, Eq, Ord)

extractBindings :: Ctx -> [(String, Ty)]
extractBindings = concatMap extractBinding
  where
    extractBinding :: Binding -> [(String, Ty)]
    extractBinding (Atom x ty)      = [(x, ty)]
    extractBinding (Pair x1 ty1 x2 ty2) = [(x1, ty1), (x2, ty2)]

genTy :: Gen Ty
genTy = sized go
  where
    go 0 = frequency [(1, return TyEps), (4, return TyInt)] 
    go n = frequency [ (1, TyCat <$> go (n `div` 8) <*> go (n `div` 8)) 
                     , (1, TyPlus <$> go (n `div` 8) <*> go (n `div` 8))
                     , (1, TyStar <$> go (n `div` 8))                   
                     , (1, return TyEps)                       
                     , (4, return TyInt)]                               

fresh :: StateT (Int, Ctx, [String]) Gen String
fresh = do
    (n, ctx, ctx') <- get
    let x = "x_" ++ show (n + 1)
    put (n + 1, ctx, ctx')
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

replaceElement :: Ctx -> String -> StateT (Int, Ctx, [String]) Gen ()
replaceElement ctx' x = do
  (n, ctx, extendedCtx) <- get
  let combinedCtx = replaceElement' ctx x ctx'
  put (n, combinedCtx, extendedCtx)

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
    | k == x = Right (v, PO.singleton (x, x))
    | otherwise = lookup' rest x
lookup' (Pair k1 v1 k2 v2 : rest) x
    | k1 == x = Right (v1, PO.singleton (k1, k1))
    | k2 == x = Right (v2, PO.singleton (k2, k2)) 
    | otherwise = lookup' rest x

bind :: Ty -> StateT (Int, Ctx, [String]) Gen String
bind s = do
  x <- fresh
  add (Atom x s)
  return x

replace :: Ctx -> StateT (Int, Ctx, [String]) Gen ()
replace ctx' = do
  (n, _, ctx'') <- get
  put (n, ctx', ctx'')

add :: Binding -> StateT (Int, Ctx, [String]) Gen ()
add el = do
  (n, ctx, ctx') <- get
  put (n, safeConcat ctx [el], ctx')

remove :: Binding -> StateT (Int, Ctx, [String]) Gen ()
remove binding = do
  (n, ctx, ctx') <- get
  let newCtx = filter (/= binding) ctx
  put (n, newCtx, ctx')

split :: StateT (Int, Ctx, [String]) Gen (Ctx, Ctx)
split = do
  (_, ctx, _) <- get
  n <- ST.lift $ choose (0, length ctx)
  let ctx0 = take n ctx
  let ctx1 = drop n ctx
  return (ctx0, ctx1)

splitAndInsert :: Ctx -> StateT (Int, Ctx, [String]) Gen ()
splitAndInsert ctx = do
  (ctx0, ctx1) <- split
  replace $ safeConcat (safeConcat ctx0 ctx) ctx1

leftOrRight :: Gen LR
leftOrRight = do elements [L, R]

choice :: Maybe Ty -> Gen LR
choice ty = do
  case ty of
    Nothing -> return NA
    Just _ -> frequency [(2, return R), (1, return L)]

dequeue :: StateT (Int, Ctx, [String]) Gen (Maybe String)
dequeue = do
  (n, ctx, ctx') <- get
  case ctx' of
    []     -> return Nothing         
    (x:xs) -> do
      put (n, ctx, xs)               
      return (Just x)               

push :: String -> StateT (Int, Ctx, [String]) Gen ()
push x = do
  (n, ctx, ctx') <- get 
  put (n, ctx, ctx' ++ [x])

pop :: StateT (Int, Ctx, [String]) Gen (Maybe String)
pop = do
  (n, ctx, ctx') <- get
  case ctx' of
    [] -> return Nothing
    _  -> do
      let (rest, lastElem) = (init ctx', last ctx') 
      put (n, ctx, rest)
      return (Just lastElem)

remove' :: String -> StateT (Int, Ctx, [String]) Gen ()
remove' name = do
  (n, ctx, ctx') <- get
  let newCtx' = filter (/= name) ctx'
  put (n, ctx, newCtx')

genTerm :: Maybe Ty -> Gen ((Term, Ty), (Int, Ctx, [String]))
genTerm maybeTy = sized (\n -> runStateT (go maybeTy R n) (0, [], []))
  where
    useBound :: Maybe Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Maybe (Term, Ty))
    useBound mty n = do
        poppedVar <- pop
        case poppedVar of
            Nothing -> return Nothing
            Just var -> do
                (_, ctx, _) <- get
                case lookup' ctx var of
                    Right (ty, _) ->
                        if mty == Nothing || mty == Just ty
                        then return $ Just (Var var ty, ty)
                        else return Nothing
                    Left _ -> return Nothing
    cons :: Maybe Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    cons t n = do
      ty <- case t of
              Just given -> return given
              Nothing -> ST.lift genTy
      let initialAcc = Nil (TyStar ty)
      let loop acc curN = 
            if curN <= 0 || depth acc > 5
            then return acc
            else do
              choice <- ST.lift $ frequency [(3, return True), (1, return False)]
              if not choice
              then return acc -- Break early by returning the accumulated term.
              else do
                (e, s) <- go (Just ty) R (curN - 1)
                loop (Cons e acc) (curN - 1)
      result <- loop initialAcc (n - 1)
      return (result, TyStar ty)
    nil :: Maybe Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    nil t n = do
      ty <- case t of
              Just given -> return given
              Nothing -> ST.lift genTy
      return (Nil ty, ty)
    starCase :: Maybe Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    starCase t n = do
      ty <- case t of
            Just given -> return given
            Nothing -> ST.lift genTy
      z <- fresh
      x <- fresh
      xs <- fresh

      lr <- ST.lift $ leftOrRight
      (e, _) <- go (Just ty) lr (n `div` 2)
      s <- ST.lift $ genTy

      splitAndInsert [Pair x s xs (TyStar s)]

      push xs
      push x

      lr' <- ST.lift $ leftOrRight
      (es, _) <- go (Just ty) lr' (n `div` 2)

      remove' x
      remove' xs

      replaceElement [Atom z (TyStar s)] x

      return (StarCase z e x xs es, ty)
    catR :: Maybe Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    catR ty n = do
      s <- case ty of
        Just (TyCat s _) -> return (Just s)
        Nothing -> return Nothing
        _ -> error ""

      t <- case ty of
        Just (TyCat _ t) -> return (Just t)
        Nothing -> return Nothing
        _ -> error ""

      choiceS <- ST.lift $ leftOrRight
      choiceT <- ST.lift $ leftOrRight

      (gamma, delta) <- split
      replace gamma
      (x, s') <- go s choiceS (n `div` 2)
      (_, gamma', _) <- get
      replace delta
      (y, t') <- go t choiceT (n `div` 2)
      (_, delta', _) <- get
      replace (safeConcat gamma' delta')
      return (CatR x y, TyCat s' t')
    plusR :: Maybe Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    plusR ty n = do
      s <- case ty of
        Just (TyPlus s _) -> return s
        Nothing -> ST.lift $ genTy
        _ -> error ""

      t <- case ty of
        Just (TyPlus _ t) -> return t
        Nothing -> ST.lift $ genTy
        _ -> error ""

      choiceS <- ST.lift $ leftOrRight
      choiceT <- ST.lift $ leftOrRight

      choice <- ST.lift $ oneof [return True, return False]
      case choice of
        True -> do
          (e1, s) <- go (Just s) choiceS (n `div` 2)
          return (InL e1 (TyPlus s t), TyPlus s t)
        False -> do
          (e2, t) <- go (Just t) choiceT (n `div` 2)
          return (InR e2 (TyPlus s t), TyPlus s t)
    var :: Maybe Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    var ty n = do
      boundVar <- useBound ty n
      case boundVar of
        Just (term, termTy) -> return (term, termTy)
        Nothing -> do
          x <- fresh
          s <- case ty of
            Nothing -> ST.lift genTy
            Just s  -> return s
          add (Atom x s)
          return (Var x s, s)
    catL :: Maybe Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    catL ty n = do
      s <- ST.lift $ genTy
      t <- ST.lift $ genTy

      x <- fresh
      y <- fresh
      z <- fresh

      choice <- ST.lift $ choice ty
      splitAndInsert [Pair x s y t]
      push y
      push x

      (e, r) <- go ty choice (n `div` 2)
      replaceElement [Atom z (TyCat s t)] x

      remove' y
      remove' x

      return (CatL x y z e, r)
    let' :: Maybe Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    let' r n = do
        x <- fresh

        (gamma0, temp) <- split
        replace temp
        (delta, gamma1) <- split

        choice <- ST.lift $ (choice r)
        replace delta
        (e, s) <- go Nothing choice (n `div` 2)
        (_, delta', _) <- get

        replace (safeConcat (safeConcat gamma0 [Atom x s]) gamma1)
        push x
        lr <- ST.lift leftOrRight
        (e', r') <- go r lr (n `div` 2)
        remove' x

        replaceElement delta' x
        return (Let x s e e', r')
    plus :: Maybe Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    plus ty n = do
      s <- ST.lift $ genTy
      t <- ST.lift $ genTy

      x <- fresh

      splitAndInsert [Atom x s]      
      choice <- ST.lift $ choice ty
      push x
      (e1, r1) <- go ty choice (n `div` 2)
      remove' x

      y <- fresh
      replaceElement [Atom y t] x
      lr <- ST.lift leftOrRight
      push y
      (e2, _) <- go (Just r1) lr (n `div` 2)
      remove' y

      z <- fresh
      replaceElement [Atom z (TyPlus s t)] y
      return (PlusCase z x e1 y e2, r1)
    lCases :: Ty -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    lCases r n = do
      (_, _, extCtx) <- get
      choice <- ST.lift $ frequency
        [ (4 * length extCtx + 1, return HVar),
          (1, return HCatL),
          (1, return HLet),
          (1, return HPlusL)
        ]
      case choice of 
        HVar -> var (Just r) n
        HCatL -> catL (Just r) n
        HLet -> let' (Just r) n
        HPlusL -> plus (Just r) n
        _ -> error ""
    go :: Maybe Ty -> LR -> Int -> StateT (Int, Ctx, [String]) Gen (Term, Ty)
    go (Just TyEps) _ _ = return (EpsR, TyEps)
    go (Just TyInt) _ _ = do
      tm <- IntR <$> ST.lift arbitrary
      return (tm, TyInt)
    go (Just r) _ 0 = do
      do
        x <- fresh
        add (Atom x r)
        return (Var x r, r)
    go (Just r) L n = lCases r (n - 1)
    go (Just (TyCat s t)) R n = catR (Just (TyCat s t)) (n - 1)
    go (Just (TyPlus s t)) R n = plusR (Just (TyPlus s t)) (n - 1)
    go (Just (TyStar s)) R n = do
      choice <- ST.lift $ frequency [
        (5, return HCons),
        (2, return HNil)]
      case choice of
        HCons -> cons (Just s) (n - 1)
        HNil -> nil (Just (TyStar s)) (n - 1)
        _ -> error ""
    go Nothing _ 0 = do
      choice <- ST.lift $ oneof [return HInt, return HEps, return HVar]
      case choice of 
        HInt -> do
          int <- IntR <$> ST.lift arbitrary
          return (int, TyInt)
        HEps -> return (EpsR, TyEps)
        HVar -> var Nothing 0
        _ -> error ""
    go Nothing _ n = do
      (_, _, extCtx) <- get
      choice <- ST.lift $ frequency
        [ (5, return HCatR),
          (5, return HCatL),
          (7, return HPlusR),
          -- (5, return HPlusL),
          (2, return HNil),
          (5, return HCons),
          -- (5, return HStarL),
          (5, return HLet),
          (7 * length extCtx + 1, return HVar),
          (2, return HInt),
          (2, return HEps)
        ]
      case choice of
        HCatR -> catR Nothing (n - 1)
        HCatL -> catL Nothing (n - 1)
        HPlusR -> plusR Nothing (n - 1)
        HPlusL -> plus Nothing (n - 1)
        HLet -> let' Nothing (n - 1)
        HVar -> var Nothing (n - 1)
        HInt -> do
          int <- IntR <$> ST.lift arbitrary
          return (int, TyInt)
        HEps -> return (EpsR, TyEps)
        HNil -> nil Nothing (n - 1)
        HCons -> cons Nothing (n - 1)
        HStarL -> starCase Nothing (n - 1)
    go maybeTy lr n = do
      (curN, ctx, ctx') <- get
      error $ trace ("Reached undefined case with parameters:\n" ++
                    "maybeTy: " ++ show maybeTy ++ "\n" ++
                    "LR: " ++ show lr ++ "\n" ++
                    "n: " ++ show n ++ "\n" ++
                    "State: " ++ show (curN, ctx, ctx')) "Unreachable code in go function"