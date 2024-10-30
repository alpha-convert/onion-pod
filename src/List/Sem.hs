module List.Sem (bigStepTerm) where
import Events
import Types
import qualified Data.Map as M
import Events (Event(CatEvA))
import Term

data Val =
      IntVal Int
    | EpsVal
    | PairVal Val Val
    | InlVal Val
    | InrVal Val

span' :: (a -> Maybe b) -> [a] -> ([b],[a])
span' f [] = ([],[])
span' f (x:xs) =
    case f x of
        Nothing -> ([],x:xs)
        Just b -> let (run,rest) = span' f xs in (b:run,rest)

parseTaggedEvents :: [TaggedEvent] -> M.Map String Val
parseTaggedEvents [] = M.empty
parseTaggedEvents ((TEV x ev):xs) =
    let (run,rest) = span' (\(TEV y ev) -> if x == y then Just ev else Nothing) xs in
    let m = parseTaggedEvents rest in
    M.insert x (parseEvents (ev:run)) m

parseEvents :: [Event] -> Val
parseEvents [] = EpsVal
parseEvents [IntEv n] = IntVal n
parseEvents (PlusPuncA : evs) = InlVal (parseEvents evs)
parseEvents (PlusPuncB : evs) = InrVal (parseEvents evs)
parseEvents (CatEvA ev : evs) =
    let (evs',CatPunc:evs'') = span' peelCatEvA evs in
    PairVal (parseEvents (ev : evs')) (parseEvents evs'')
        where
            peelCatEvA (CatEvA ev) = Just ev
            peelCatEvA _ = Nothing
parseEvents (CatPunc:evs) = parseEvents evs
parseEvents _ = error ""



serialize :: Val -> [Event]
serialize EpsVal = []
serialize (IntVal n) = [IntEv n]
serialize (PairVal v1 v2) = (CatEvA <$> serialize v1) ++ [CatPunc] ++ serialize v2
serialize (InlVal v) = PlusPuncA : serialize v
serialize (InrVal v) = PlusPuncB : serialize v

eval :: Term -> M.Map String Val -> Val
eval EpsR m = EpsVal
eval (Var x _) m =
    case M.lookup x m of
        Just v -> v
eval (IntR n) _ = IntVal n
eval (CatL x y z e) m =
    case M.lookup z m of
        Just (PairVal v1 v2) -> eval e (M.insert x v1 (M.insert y v2 m))
eval (CatR e e') m = PairVal (eval e m) (eval e' m)
eval (InL e) m = InlVal (eval e m)
eval (InR e) m = InrVal (eval e m)
eval (PlusCase z x e y e') m =
    case M.lookup z m of
        Just (InlVal v) -> eval e (M.insert x v m)
        Just (InrVal v) -> eval e (M.insert y v m)
eval Nil m = InlVal EpsVal
eval (Cons e e') m = InrVal (PairVal (eval e m) (eval e' m))
eval (StarCase xs e y ys e') m =
    case M.lookup xs m of
        Just (InlVal EpsVal) -> eval e m
        Just (InrVal (PairVal v1 v2)) -> eval e' (M.insert y v1 (M.insert ys v2 m))
eval (Let x e e') m = eval e' (M.insert x (eval e m) m)

eval (Fix _) _ = error "unimplemented."
eval Rec _ = error "unimplemented."

bigStepTerm :: Term -> [TaggedEvent] -> [Event]
bigStepTerm e xs =
    let m = parseTaggedEvents xs in
    serialize (eval e m)