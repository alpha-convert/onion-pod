{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
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



sem2 :: ElimTerm -> StreamFunc s TaggedEvent -> StreamFunc (s,RunState) Event
sem2 (EUse (VarElim y) s) (SF i0 next) = SF (i0,STy s) $ \(i,STy s) ->
    if isNull s then Done
    else case next i of
            -- TODO: We might need to distinguish an ``input done'' vs ``output done'' branch. The output done will carry the input state.
            -- Maybe we can also break the step function apart into:
            -- Step s s' a
            Done -> Done
            Skip i' -> Skip (i',STy s)
            Yield (TEV x ev) i' -> if x == y then Yield ev (i', STy (deriv s ev)) else Skip (i',STy s)
            -- if isNull s
            -- then Done
            -- else case nextFromElim x' c of
                    -- Done -> Done
                    -- Skip (x'',c') -> Skip (x'',EUse c' s)
                    -- Yield ev (x'',c') -> Yield ev (x'', EUse c' (deriv s ev))
sem2 EEpsR (SF x0 _) = SF (x0,SUnit) (const Done)
sem2 (EIntR n) (SF x0 _) = SF (x0,SBool False) (\(x,SBool b) -> if b then Done else Yield (IntEv n) (x,SBool True))
sem2 (ECatR e1 e2) s@(SF i0 _) =
    let (SF (_,x0) next) = sem2 e1 s in
    let (SF (_,y0) next') = sem2 e2 s in
    SF (i0,SInL x0) $ \case
                        (i,SInL x) -> case next (i,x) of
                                        Yield ev (i',x') -> Yield (CatEvA ev) (i',SInL x')
                                        Skip (i',x') -> Skip (i',SInL x')
                                        Done -> Yield CatPunc (i,SInR y0)
                        (i,SInR y) -> case next' (i,y) of
                                        Done -> Done
                                        Skip (i',y') -> Skip (i',SInR y')
                                        Yield ev (i',y') -> Yield ev (i',SInR y')
sem2 _ _ = undefined