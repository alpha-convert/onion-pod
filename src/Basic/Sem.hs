{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Basic.Sem where

import ElimTerm
import Basic.Stream
import Events
import Types

{-
Definitional interpreter. It just runs the interpreter for a step!
-}
definitional :: ElimTerm -> StreamFunc s TaggedEvent -> StreamFunc (s,ElimTerm) Event
definitional e (SF x0 next_in) = SF (x0,e) next
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

        next (x', EFix _ _ _) = error "Unimplemented"
        next (x', ERec _) = error "Unimplemented"

definitional' :: ElimTerm -> Stream TaggedEvent -> Stream Event
definitional' a (S sf) = S (definitional a sf)


semElim :: Elim -> StreamFunc s TaggedEvent -> StreamFunc (s,RunState) Event
semElim (VarElim y) (SF i0 next) = SF (i0,SUnit) $
    \(i,_) -> case next i of
                    Done -> Done
                    Skip i' -> Skip (i',SUnit)
                    Yield (TEV z ev) i' -> if z == y then Yield ev (i',SUnit) else Skip (i',SUnit)

semElim (Proj1Elim c) s =
    let (SF (i0,x0) nextC) = semElim c s in
    SF (i0,x0) $ \(i,x) -> case nextC (i,x) of
                            Done -> Done
                            Skip (i',x') -> Skip (i',x')
                            Yield (CatEvA ev) (i',x') -> Yield ev (i',x')
                            Yield _ _ -> error ""

semElim (Proj2Elim c) s =
    let (SF (i0,x0) nextC) = semElim c s in
    SF (i0,SInL x0) $ \case
                        (i,SInL x) -> case nextC (i,x) of
                                        Done -> Done
                                        Skip (i',x') -> Skip (i',SInL x')
                                        Yield (CatEvA _) (i',x') -> Skip (i',SInL x')
                                        Yield CatPunc (i',x') -> Skip (i',SInR x') --switch states
                        (i,SInR x) -> nextC (i,x)

semElim (LetElim e) s = semElimTerm e s

semElimTerm :: ElimTerm -> StreamFunc s TaggedEvent -> StreamFunc (s,RunState) Event
semElimTerm (EUse c t) s =
    let (SF (i0,x0) nextElim) = semElim c s in
    SF (i0,SPair x0 (STy t)) $ \(i,SPair x (STy t)) ->
    if isNull t then Done
    else case nextElim (i,x) of
            -- TODO: We might need to distinguish an ``input done'' vs ``output done'' branch. The output done will carry the input state.
            -- Maybe we can also break the step function apart into:
            -- Step s s' a
            Done -> Done
            Skip (i',x') -> Skip (i',SPair x' (STy t))
            Yield ev (i',x') -> Yield ev (i', SPair x' (STy (deriv t ev)))

semElimTerm EEpsR (SF x0 _) = SF (x0,SUnit) (const Done)
semElimTerm (EIntR n) (SF x0 _) = SF (x0,SBool False) (\(x,SBool b) -> if b then Done else Yield (IntEv n) (x,SBool True))
semElimTerm (ECatR e1 e2) s@(SF i0 _) =
    let (SF (_,x0) next) = semElimTerm e1 s in
    let (SF (_,y0) next') = semElimTerm e2 s in
    SF (i0,SInL x0) $ \case
                        (i,SInL x) -> case next (i,x) of
                                        Yield ev (i',x') -> Yield (CatEvA ev) (i',SInL x')
                                        Skip (i',x') -> Skip (i',SInL x')
                                        Done -> Yield CatPunc (i,SInR y0)
                        (i,SInR y) -> case next' (i,y) of
                                        Done -> Done
                                        Skip (i',y') -> Skip (i',SInR y')
                                        Yield ev (i',y') -> Yield ev (i',SInR y')
semElimTerm (EPlusCase c e1 e2) s =
    let (SF (i0,cx0) nextSem) = semElim c s in
    let (SF (_,x0) next1) = semElimTerm e1 s in
    let (SF (_,y0) next2) = semElimTerm e2 s in
    SF (i0,SInL cx0) $ \case
                            (i,SInL cx) -> case nextSem (i,cx) of
                                             Done -> Done
                                             Skip (i',cx') -> Skip (i',SInL cx')
                                             Yield PlusPuncA (i',_) -> Skip (i',SInR (SInL x0))
                                             Yield PlusPuncB (i',_) -> Skip (i',SInR (SInR y0))
                            -- THIS IS A MONOTNE TRANITION -- we're never gonna go back to SInL. We should figur eout how to eliminate this case after it's taken.
                            (i,SInR (SInL x)) -> case next1 (i,x) of
                                                    Done -> Done
                                                    Skip (i',x') -> Skip (i',SInR (SInL x'))
                                                    Yield ev (i',x') -> Yield ev (i',SInR (SInL x'))
                            (i,SInR (SInR y)) -> case next2 (i,y) of
                                                    Done -> Done
                                                    Skip (i',y') -> Skip (i',SInR (SInR y'))
                                                    Yield ev (i',y') -> Yield ev (i',SInR (SInR y'))

semElimTerm (EFix xs es e) _ = undefined
semElimTerm (ERec es) _ = undefined
semElimTerm _ _ = undefined