{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
module PullSemCPS where

import ElimTerm
import StreamCPS
import Events
import Types

denoteElimTermCps :: ElimTerm -> StreamFuncCps s TaggedEvent -> StreamFuncCps (s, ElimTerm) Event
denoteElimTermCps e (SFCps @s x0 next) = SFCps (x0, e) next'
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

denoteElimTermCps' :: ElimTerm -> StreamCps TaggedEvent -> StreamCps Event
denoteElimTermCps' e (S sf) = S (denoteElimTermCps e sf)