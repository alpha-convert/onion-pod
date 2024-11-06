{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Basic.NormalizedSem where

import NormalForm
import Basic.Stream
import Events
import Types

semNe :: Ne a -> StreamFunc s TaggedEvent -> (forall w. (forall s'. StreamFunc (s,s') Event -> w) -> w)
semNe ne = _

semNf :: Nf a -> StreamFunc s TaggedEvent -> (forall w. (forall s'. StreamFunc (s,s') Event -> w) -> w)
semNf (NUp ne) s = semNe ne s
semNf (NCatL (NVar x) k) _ = _

-- semElimTerm :: ElimTerm -> StreamFunc s TaggedEvent -> StreamFunc (s,RunState) Event
-- semElimTerm (EUse c t) s =
--     let (SF (i0,x0) nextElim) = semElim c s in
--     SF (i0,SPair x0 (STy t)) $ \(i,SPair x (STy t)) ->
--     if isNull t then Done
--     else case nextElim (i,x) of
--             -- TODO: We might need to distinguish an ``input done'' vs ``output done'' branch. The output done will carry the input state.
--             -- Maybe we can also break the step function apart into:
--             -- Step s s' a
--             Done -> Done
--             Skip (i',x') -> Skip (i',SPair x' (STy t))
--             Yield ev (i',x') -> Yield ev (i', SPair x' (STy (deriv t ev)))

-- semElimTerm EEpsR (SF x0 _) = SF (x0,SUnit) (const Done)
-- semElimTerm (EIntR n) (SF x0 _) = SF (x0,SBool False) (\(x,SBool b) -> if b then Done else Yield (IntEv n) (x,SBool True))
-- semElimTerm (ECatR e1 e2) s@(SF i0 _) =
--     let (SF (_,x0) next) = semElimTerm e1 s in
--     let (SF (_,y0) next') = semElimTerm e2 s in
--     SF (i0,SInL x0) $ \case
--                         (i,SInL x) -> case next (i,x) of
--                                         Yield ev (i',x') -> Yield (CatEvA ev) (i',SInL x')
--                                         Skip (i',x') -> Skip (i',SInL x')
--                                         Done -> Yield CatPunc (i,SInR y0)
--                         (i,SInR y) -> case next' (i,y) of
--                                         Done -> Done
--                                         Skip (i',y') -> Skip (i',SInR y')
--                                         Yield ev (i',y') -> Yield ev (i',SInR y')
-- semElimTerm (EPlusCase c e1 e2) s =
--     let (SF (i0,cx0) nextSem) = semElim c s in
--     let (SF (_,x0) next1) = semElimTerm e1 s in
--     let (SF (_,y0) next2) = semElimTerm e2 s in
--     SF (i0,SInL cx0) $ \case
--                             (i,SInL cx) -> case nextSem (i,cx) of
--                                              Done -> Done
--                                              Skip (i',cx') -> Skip (i',SInL cx')
--                                              Yield PlusPuncA (i',_) -> Skip (i',SInR (SInL x0))
--                                              Yield PlusPuncB (i',_) -> Skip (i',SInR (SInR y0))
--                             -- THIS IS A MONOTNE TRANITION -- we're never gonna go back to SInL. We should figur eout how to eliminate this case after it's taken.
--                             (i,SInR (SInL x)) -> case next1 (i,x) of
--                                                     Done -> Done
--                                                     Skip (i',x') -> Skip (i',SInR (SInL x'))
--                                                     Yield ev (i',x') -> Yield ev (i',SInR (SInL x'))
--                             (i,SInR (SInR y)) -> case next2 (i,y) of
--                                                     Done -> Done
--                                                     Skip (i',y') -> Skip (i',SInR (SInR y'))
--                                                     Yield ev (i',y') -> Yield ev (i',SInR (SInR y'))

-- semElimTerm (EFix e) _ = undefined
-- semElimTerm ERec s = undefined
-- semElimTerm _ _ = undefined