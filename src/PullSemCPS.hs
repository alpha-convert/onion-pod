{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
module PullSemCPS where

import ElimTerm
import StreamCPS
import Events
import Types

denoteElimTermCps :: ElimTerm -> StreamFunc s TaggedEvent -> StreamFunc (s, ElimTerm) Event
denoteElimTermCps e (SF @s x0 next) = SF (x0, e) next'
  where
    nextFromElim :: forall w. 
        s -> Elim -> w -> 
            ((s, Elim) -> w) -> 
                (Event -> (s, Elim) -> w) -> w
    nextFromElim x' (VarElim y) done skip yield = 
        next x' 
            done 
            --- Advance the state.
            (\x'' -> skip (x'', VarElim y))
            (\(TEV z ev) x'' -> if z == y 
            {-
                If the tag matches the variable, yield 
                the event and a tuple of the updated
                state + the variable.
            -}
                                then yield ev (x'', VarElim y) 
                                else skip (x'', VarElim y))
    nextFromElim x' (Proj1Elim c) done skip yield = 
        nextFromElim x' c
            done
            (\(x'', c') -> skip (x'', Proj1Elim c'))
            (\ev (x'', c') -> case ev of
                CatEvA ev' -> yield ev' (x'', Proj1Elim c')
                _ -> error "Unexpected event in Proj1Elim."
            )
    --- A little confused about this case.
    nextFromElim x' (Proj2Elim c) done skip _ = 
        nextFromElim x' c
            done
            (\(x'', c') -> skip (x'', Proj2Elim c'))
            (\ev (x'', c') -> case ev of
                CatEvA _ -> skip (x'', Proj2Elim c')
                CatPunc -> skip (x'', c')
                _ -> error "Unexpected event in Proj2Elim."
            )
    --- Haven't discussed this one much.
    nextFromElim x' (LetElim e') done skip yield = 
        next' (x', e') 
            done
            (\(x'', e'') -> skip (x'', LetElim e''))
            (\ev (x'', e'') -> yield ev (x'', LetElim e''))
    next' :: forall w. 
        (s, ElimTerm) -> 
            w -> ((s, ElimTerm) -> w) -> 
                (Event -> (s, ElimTerm) -> w) -> w
    next' (x', EUse c s) done skip yield
        | isNull s = done
        | otherwise = 
            nextFromElim x' c 
                done
                (\(x'', c') -> skip (x'', EUse c' s)) 
                (\ev (x'', c') -> yield ev (x'', EUse c' (deriv s ev)))

    next' (x', EIntR n) _ _ yield = yield (IntEv n) (x', EEpsR)

    next' (_, EEpsR) done _ _ = done

    next' (x', ECatR e1 e2) _ skip yield =
        next' (x', e1)
            --- When done, yield punctuation indicating that
            --- the first part of the stream has finished.
            (yield CatPunc (x', e2))
            --- Step without producing output.
            (\(x'', e1') -> skip (x'', ECatR e1' e2))
            --- Wrap the event in a CatEvA term so we know what part
            --- of the stream it belongs to.
            (\ev (x'', e1') -> yield (CatEvA ev) (x'', ECatR e1' e2))

    next' (x', EInL e') _ _ yield = yield PlusPuncA (x', e')
    next' (x', EInR e') _ _ yield = yield PlusPuncB (x', e')

    next' (x', EPlusCase c e1 e2) done skip _ =
        nextFromElim x' c
            done
            (\(x'', c') -> skip (x'', EPlusCase c' e1 e2))
            (\ev (x'', _) -> case ev of
                PlusPuncA -> skip (x'', e1)
                PlusPuncB -> skip (x'', e2)
                _ -> error "Unexpected event in PlusCase."
            )
    
    next' (_, EFix _) _ _ _ = error "Not yet implemented."
    next' (_, ERec) _ _ _ = error "We don't know how to do this yet."

denoteElimTermCps' :: ElimTerm -> Stream TaggedEvent -> Stream Event
denoteElimTermCps' e (S sf) = S (denoteElimTermCps e sf)



semElim :: Elim -> StreamFunc s TaggedEvent -> StreamFunc (s,RunState) Event
semElim (VarElim y) (SF i0 next) = SF (i0,SUnit) $
    \(i,_) -> next i _ _ _
                    -- Done -> Done
                    -- Skip i' -> Skip (i',SUnit)
                    -- Yield (TEV z ev) i' -> if z == y then Yield ev (i',SUnit) else Skip (i',SUnit)

semElim (Proj1Elim c) s =
    let (SF (i0,x0) nextC) = semElim c s in
    SF (i0,x0) $ \(i,x) -> nextC (i,x) _ _ _
                            -- Done -> Done
                            -- Skip (i',x') -> Skip (i',x')
                            -- Yield (CatEvA ev) (i',x') -> Yield ev (i',x')
                            -- Yield _ _ -> error ""

semElim (Proj2Elim c) s =
    let (SF (i0,x0) nextC) = semElim c s in
    SF (i0,SInL x0) $ \case
                        (i,SInL x) -> nextC (i,x) _ _ _
                                        -- Done -> Done
                                        -- Skip (i',x') -> Skip (i',SInL x')
                                        -- Yield (CatEvA _) (i',x') -> Skip (i',SInL x')
                                        -- Yield CatPunc (i',x') -> Skip (i',SInR x') --switch states
                        (i,SInR x) -> nextC (i,x) _ _ _

semElim (LetElim e) s = semElimTerm e s

semElimTerm :: ElimTerm -> StreamFunc s TaggedEvent -> StreamFunc (s,RunState) Event
semElimTerm (EUse c t) s =
    let (SF (i0,x0) nextElim) = semElim c s in
    SF (i0,SPair x0 (STy t)) $ \(i,SPair x (STy t)) ->
    if isNull t then Done
    else nextElim (i,x) _ _ _
            -- Done -> Done
            -- Skip (i',x') -> Skip (i',SPair x' (STy t))
            -- Yield ev (i',x') -> Yield ev (i', SPair x' (STy (deriv t ev)))
semElimTerm EEpsR (SF x0 _) = SF (x0,SUnit) (\_ done _ _ -> done)
semElimTerm (EIntR n) (SF x0 _) = SF (x0,SBool False) (\(x,SBool b) done skip yield -> if b then done else yield (IntEv n) (x,SBool True))
semElimTerm (ECatR e1 e2) s@(SF i0 _) =
    let (SF (_,x0) next) = semElimTerm e1 s in
    let (SF (_,y0) next') = semElimTerm e2 s in
    SF (i0,SInL x0) $ \case
                        (i,SInL x) -> next (i,x) _ _ _
                                        -- Yield ev (i',x') -> Yield (CatEvA ev) (i',SInL x')
                                        -- Skip (i',x') -> Skip (i',SInL x')
                                        -- Done -> Yield CatPunc (i,SInR y0)
                        (i,SInR y) -> next' (i,y) _ _ _
                                        -- Done -> Done
                                        -- Skip (i',y') -> Skip (i',SInR y')
                                        -- Yield ev (i',y') -> Yield ev (i',SInR y')
semElimTerm (EPlusCase c e1 e2) s =
    let (SF (i0,cx0) nextSem) = semElim c s in
    let (SF (_,x0) next1) = semElimTerm e1 s in
    let (SF (_,y0) next2) = semElimTerm e2 s in
    SF (i0,SInL cx0) $ \case
                            (i,SInL cx) -> nextSem (i,cx) _ _ _
                                            --  Done -> Done
                                            --  Skip (i',cx') -> Skip (i',SInL cx')
                                            --  Yield PlusPuncA (i',_) -> Skip (i',SInR (SInL x0))
                                            --  Yield PlusPuncB (i',_) -> Skip (i',SInR (SInR y0))
                            -- THIS IS A MONOTNE TRANITION -- we're never gonna go back to SInL. We should figur eout how to eliminate this case after it's taken.
                            (i,SInR (SInL x)) -> next1 (i,x) _ _ _
                                                    -- Done -> Done
                                                    -- Skip (i',x') -> Skip (i',SInR (SInL x'))
                                                    -- Yield ev (i',x') -> Yield ev (i',SInR (SInL x'))
                            (i,SInR (SInR y)) -> next2 (i,y) _ _ _
                                                    -- Done -> Done
                                                    -- Skip (i',y') -> Skip (i',SInR (SInR y'))
                                                    -- Yield ev (i',y') -> Yield ev (i',SInR (SInR y'))

semElimTerm _ _ = undefined