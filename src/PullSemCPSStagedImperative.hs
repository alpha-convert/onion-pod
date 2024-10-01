
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell #-}

module PullSemCPSStagedImperative where
import ElimTerm
import StatefulTemplateStream
import Events
import Types
import Language.Haskell.TH
import Data.STRef
import Data.Function

semElim :: (Quote m) => Elim -> IStream m t i TaggedEvent -> Stream m t i Event
semElim (VarElim y) (IS init next) = S init $ SF (\k -> k ()) $
    \i _ done skip yield -> next i done skip (\ctev -> [||
            let (TEV z ev) = $$ctev in
            if z == y then $$(yield [||ev||]) else $$skip
        ||])

semElim (Proj1Elim c) s =
    semElim c s & \(S iinit (SF cinit nextC)) ->
    S iinit $ SF cinit $
        \i s' done skip yield -> nextC i s' done skip $
            \cev -> [||
                        case $$cev of
                            CatEvA ev -> $$(yield [||ev||])
                    ||]

semElim (Proj2Elim c) s =
    semElim c s & \(S iinit (SF cinit nextC)) ->
    S iinit $ SF (\k -> cinit (\x0 -> [|| do {seenCatPunc <- newSTRef False; $$(k (x0,[||seenCatPunc||]))} ||]))
                 (\i (x,cref) done skip yield -> [|| do
                        b <- readSTRef $$cref;
                        if b then $$(nextC i x done skip yield) else
                            $$(nextC i x done skip 
                                (\cev -> [||
                                    case $$cev of
                                        CatEvA _ -> $$skip
                                        CatPunc -> writeSTRef $$cref True >> $$skip
                                ||])
                              )
                 ||])

semElim (LetElim e) s = semElimTerm e s

semElimTerm :: (Quote m) => ElimTerm -> IStream m t i TaggedEvent -> Stream m t i Event
semElimTerm (EUse c t) s = undefined

semElimTerm EEpsR (IS iinit _) = S iinit $ SF ($ ()) $ \_ _ done _ _ -> done

semElimTerm (EIntR n) (IS iinit _) = S iinit $ SF 
    (\k -> [|| do {intSent <- newSTRef False; $$(k [||intSent||])} ||]) --Another piece of state that should be control. Basically everything should be except for actual state!
    (\_ cref done _ yield -> [|| do
        b <- readSTRef $$cref;
        if b then $$done else writeSTRef $$cref True >> $$(yield [||(IntEv n)||])
    ||])

semElimTerm (ECatR e1 e2) s =
    semElimTerm e1 s & \(S iinit (SF xinit next1)) ->
    semElimTerm e2 s & \(S _ (SF yinit next2)) ->
    -- Once again, control should be control! Not state that you branch on.
    S iinit $ SF (\k -> xinit (\x -> yinit (\y -> [|| do { finished_e1 <- newSTRef False; $$(k (x,y,[||finished_e1||]))} ||]))) $
        \i (x,y,crfinished) done skip yield -> [|| do
            e1_done <- readSTRef $$crfinished
            if not e1_done then
                $$(next1 i x [|| writeSTRef $$crfinished True >> $$(yield [|| CatPunc ||]) ||] skip (\cev -> yield [|| CatEvA $$cev||]))
            else
                $$(next2 i y done skip yield)
        ||]

{-
semElimTerm (ECatR e1 e2) s@(SF _ _) =
    let (SF cix0 next) = semElimTerm e1 s in
    let (SF ciy0 next') = semElimTerm e2 s in
    SF [||let (i0,x0) = $$cix0 in (i0,SInL x0)||] $
        \cist done skip yield -> [||
            let (i,st) = $$cist in
            let (_,y0) = $$ciy0 in
            case st of
                SInL x -> $$(next [||(i,x)||]
                                    (yield [||CatPunc||] [||(i,SInR y0)||])
                                    (\cix' -> skip [||let (i',x') = $$cix' in (i',SInL x')||])
                                    (\cev cix' -> yield [||CatEvA $$cev||] [||let (i',x') = $$cix' in (i',SInL x')||])
                            )
                SInR y -> $$(next' [||(i,y)||]
                                    done
                                    (\ciy' -> skip [||let (i',y') = $$ciy' in (i',SInR y')||])
                                    (\cev ciy' -> yield cev [||let (i',y') = $$ciy' in (i',SInR y')||]))
        ||]

-}

{-
HMM. as currently implemented this'll allocate for both branches at the beginning. This is bad, we want
to allocate locally.

semElimTerm (EPlusCase c e1 e2) s =
    let (SF cicx0 nextSem) = semElim c s in
    let (SF cix0 next1) = semElimTerm e1 s in
    let (SF ciy0 next2) = semElimTerm e2 s in
    SF [|| let (i0,cx0) = $$cicx0 in (i0,SInL cx0) ||] (
        \ist done skip yield -> [||
            let (i,st) = $$ist in
            case st of
                SInL cx -> $$(nextSem [|| (i,cx) ||] done
                              (\cicx' -> [|| let (i',cx') = $$cicx' in $$(skip [|| (i',SInL cx') ||]) ||])
                              (\cev cicx' ->
                                [||
                                    let ev = $$cev in
                                    let (i',_) = $$cicx' in
                                    case ev of
                                        PlusPuncA -> $$(skip [|| let (_,x0) = $$cix0 in (i',SInR (SInL x0)) ||])
                                        PlusPuncB -> $$(skip [|| let (_,y0) = $$ciy0 in (i',SInR (SInR y0)) ||])
                                        _ -> error ""
                                ||]
                              )
                             )
                -- SInR (SInL x) -> next1 (i,x) done (\(i',x') -> skip (i',SInR (SInL x'))) (\ev (i',x') -> yield ev (i',SInR (SInL x')))
                SInR (SInL x) -> $$(next1 [|| (i,x) ||] done 
                                        (\cix' -> [|| let (i',x') = $$cix' in $$(skip [|| (i',SInR (SInL x')) ||]) ||])
                                        (\ca cix' -> [|| let a = $$ca in let (i',x') = $$cix' in $$(yield [|| a ||] [|| (i',SInR (SInL x')) ||]) ||])
                                    )
                SInR (SInR y) -> $$(next2 [|| (i,y) ||] done 
                                        (\ciy' -> [|| let (i',y') = $$ciy' in $$(skip [|| (i',SInR (SInR y')) ||]) ||])
                                        (\ca ciy' -> [|| let a = $$ca in let (i',y') = $$ciy' in $$(yield [|| a ||] [|| (i',SInR (SInR y')) ||]) ||])
                                    )
        ||]
     )

-}

semElimTerm _ _ = undefined
