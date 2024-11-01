module TypeCheck where

import PartialOrder as PO
import Test.QuickCheck
import ElimTerm
import Term
import Types
import Events
import Control.Monad.State as ST
import Control.Monad ( when, foldM, replicateM )
import Test.Hspec
import Basic.Sem
import Basic.Stream
import Language.Haskell.TH.Syntax
import List.Sem

data Error = TypeMismatch
           | OrderViolation (Maybe String) (Maybe String) String
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
                then return (st, eOrder)
                else Left $ OrderViolation (Just x) (Just y) "CatL'"
          _ -> Left $ TypeMismatch

check ctx (InL e _) st =
    case st of 
        (TyPlus s _) -> check ctx e s
        _ -> Left $ TypeMismatch

check ctx (InR e _) st =
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
                orderUnion "PlusCase'-U" r e1Order e2Order >>= \(_, eOrders) ->
                orderSequential r zOrder eOrders
        _ -> Left $ TypeMismatch

check ctx (StarCase z e x xs es) r =
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

check ctx (Let x s e e') r = do
    check ctx e s >>= \(_, eUses) ->
      check (safeConcat ctx [(Atom x s)]) e' r >>= \(e't, e'Uses) ->
        let all_e_vars = concatMap (\(a, b) -> [a, b]) (PO.toList eUses) in
        orderUnion "Let'-U" e't eUses (PO.substAll all_e_vars x e'Uses)

check _ term _ = Left $ NotImplemented term

generateTaggedEvents :: Ctx -> Gen [TaggedEvent]
generateTaggedEvents ctx = do
    let bindings = extractBindings ctx 
    genTaggedEventsForContext bindings
