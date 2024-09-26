module ElimTerm where

import Events
import Types
import Term
import qualified Data.Map as Map
import Stream

{- Are Elims just a focusing thing? -}
data Elim = VarElim String
        --   | HistVarElim String
          | Proj1Elim Elim
          | Proj2Elim Elim
          | LetElim ElimTerm
          deriving (Eq,Ord,Show)

{-
Elimnel tying:

-------------------------
G;x:s;G' |- VarElim x : s

G |- c : s . t
---------------------
G |- Proj1Elim c : s

G |- c : s . t
---------------------
G |- Proj2Elim c : t

-}

{- Removes all Pi2s from an eliminator. If we've gotten at least one event through an eliminator, it has to have no more pi2s in it... -}
delPi2 :: Elim -> Elim
delPi2 (VarElim x) = VarElim x
delPi2 (Proj1Elim c) = Proj1Elim (delPi2 c)
delPi2 (Proj2Elim c) = delPi2 c
delPi2 (LetElim e) = LetElim e

{- if elim is an eliminator with underlying variable x, and ev is an event from the channel x,
then elimDeriv elim ev is the eliminator updated after the event
-}

{- absolutely no idea how i came up with the code for this. -}
elimDeriv :: Elim -> Event -> Elim
elimDeriv el ev = go el ev const
    where
        go (VarElim x) ev k = k (VarElim x) (Just ev)
        go (Proj1Elim el) ev k = go el ev (\el' ev ->
            case ev of
                Nothing -> k (Proj1Elim el') Nothing
                Just (CatEvA ev') -> k (Proj1Elim el') (Just ev')
                Just ev -> error $ "Unexpected event " ++ show ev ++ " in elimderiv"
         )
        go (Proj2Elim el) ev k = go el ev (\el' ev ->
            case ev of
                Nothing -> k (Proj2Elim el') Nothing
                Just (CatEvA _) -> k (Proj2Elim el') Nothing
                Just CatPunc -> k el' Nothing
                Just ev -> error $ "Unexpected event " ++ show ev ++ " in elimderiv"
         )
        -- UHH no idea.
        go (LetElim e) ev k = k (LetElim e) (Just ev)


data ElimTerm =
      EEpsR
    | EUse Elim Ty
    | EIntR Int
    | ECatR ElimTerm ElimTerm
    | EInR ElimTerm
    | EInL ElimTerm
    | EPlusCase Elim ElimTerm ElimTerm
    | EFix ElimTerm
    -- | EWait String Ty ElimTerm
    | ERec
    deriving (Eq,Ord,Show)

fixSubst :: ElimTerm -> ElimTerm -> ElimTerm
fixSubst = undefined

inlineElims :: Term -> ElimTerm
inlineElims e = go mempty e
    where
        getElim m x = case Map.lookup x m of
                      Nothing -> VarElim x
                      Just c -> c
        go _ EpsR = EEpsR
        go _ (IntR n) = EIntR n
        go m (Var x s) = EUse (getElim m x) s
        -- go m (IntCase z e1 y e2) =
        --     let c = getElim m z in
        --     EIntCase c (go m e1) (go (Map.insert y (PredElim (delPi2 c)) m) e2)
        go m (CatR e1 e2) = ECatR (go m e1) (go m e2)
        go m (CatL x y z e) =
            let c = getElim m z in
            go (Map.insert x (Proj1Elim c) (Map.insert y (Proj2Elim c) m)) e
        go m (InL e) = EInL (go m e)
        go m (InR e) = EInR (go m e)
        go m (PlusCase z x e1 y e2) =
            let c = getElim m z in
            EPlusCase c (go (Map.insert x (delPi2 c) m) e1) (go (Map.insert y (delPi2 c) m) e2)
        go m Nil = EInL EEpsR
        go m (Cons e1 e2) = EInR (ECatR (go m e1) (go m e2))
        go m (StarCase z e1 x xs e2) =
            let c = getElim m z in
            EPlusCase c (go m e1) (go (Map.insert x (Proj1Elim (delPi2 c)) (Map.insert xs (Proj2Elim (delPi2 c)) m)) e2)
        -- go m (Wait x s e) = EWait x s (go (Map.insert x (HistVarElim x) m) e)
        go m (Fix e) = EFix (go m e)
        go _ Rec = ERec
        go m (Let x e e') = go (Map.insert x (LetElim (go m e)) m) e'


denoteElimTerm :: ElimTerm -> StreamFunc s TaggedEvent -> StreamFunc (s,ElimTerm) Event
denoteElimTerm e (SF x0 next_in) = SF (x0,e) next
    where
        nextFromElim x' (VarElim x) =
            case next_in x' of
                Done -> Done
                Skip x'' -> Skip (x'',VarElim x)
                Yield (TEV z ev) x'' -> if z == x then Yield ev (x'',VarElim x) else Skip (x'',VarElim x)

        nextFromElim x' (Proj1Elim c) =
            case nextFromElim x' c of
                Done -> Done
                Skip (x'',c') -> Skip (x'',Proj1Elim c')
                Yield (CatEvA ev) (x'',c') -> Yield ev (x'', Proj1Elim c')
                Yield {} -> error ""

        nextFromElim x' (Proj2Elim c) =
                case nextFromElim x' c of
                    Done -> Done
                    Skip (x'',c') -> Skip (x'',Proj2Elim c')
                    Yield (CatEvA _) (x'',c') -> Skip (x'', Proj2Elim c')

                    Yield CatPunc (x'',c') -> Skip (x'', c') -- peel off the proj2. this is probably not an ideal way to do this, but oh well. should really be in-place.

                    Yield {} -> error ""
        
        nextFromElim x' (LetElim e) =
            case next (x',e) of
                Done -> Done
                Skip (x',e') -> Skip (x', LetElim e')
                Yield ev (x',e') -> Yield ev (x',LetElim e')
        

        next (x',EUse c s) =
            if isNull s
            then Done
            else case nextFromElim x' c of
                    Done -> Done
                    Skip (x'',c') -> Skip (x'',EUse c' s)
                    Yield ev (x'',c') -> Yield ev (x'', EUse c' (deriv s ev))

        next (x',EIntR n) = Yield (IntEv n) (x',EEpsR)

        next (x',EEpsR) = Done

        next (x',ECatR e1 e2) =
            case next (x',e1) of
                Skip (x'',e1') -> Skip (x'',ECatR e1' e2)
                Yield ev (x'',e1') -> Yield (CatEvA ev) (x'',ECatR e1' e2)
                Done -> Yield CatPunc (x',e2)

        next (x',EInL e) = Yield PlusPuncA (x',e)
        next (x',EInR e) = Yield PlusPuncB (x',e)

        next (x',EPlusCase c e1 e2) =
            case nextFromElim x' c of
                Done -> Done
                Skip (x',c') -> Skip (x',EPlusCase c' e1 e2)
                Yield PlusPuncA (x',_) -> Skip (x',e1)
                Yield PlusPuncB (x',_) -> Skip (x',e2)
                Yield ev _ -> error $ "Unexpected event " ++ show ev ++ " from pluscase"

        next (x', EFix e) = Skip (x', fixSubst (EFix e) e)
        next (x', ERec) = error ""

denoteElimTerm' :: ElimTerm -> Stream TaggedEvent -> Stream Event
denoteElimTerm' a (S sf) = S (denoteElimTerm a sf)

-- TaggedEvent = (String,Event)
