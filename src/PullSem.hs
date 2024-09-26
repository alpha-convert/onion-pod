module PullSem where

import ElimTerm
import Stream
import Events
import Types

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
