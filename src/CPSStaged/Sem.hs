
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell #-}

module CPSStaged.Sem where
import ElimTerm
import CPSStaged.Stream
import Events
import Types
import Language.Haskell.TH

denoteElimTerm' :: (Quote m) => ElimTerm -> StreamFunc m s TaggedEvent -> StreamFunc m (s, ElimTerm) Event
denoteElimTerm' e (SF @m @s x0 next) = SF [|| ($$x0, e) ||] next'
  where
    -- Can we give this the type:
    -- nextFromElim :: (Quote m) => forall w. Code m s -> Code m Elim -> Code m w ->  (Code m s -> Code m Elim -> Code m w) ->  (Code m Event -> Code m s -> Code m Elim -> Code m w) -> Code m w
    nextFromElim :: (Quote m) => forall w. Code m s -> Code m Elim -> Code m w ->  (Code m (s, Elim) -> Code m w) ->  (Code m Event -> Code m (s, Elim) -> Code m w) -> Code m w
    nextFromElim cx ce done skip yield = [||
        case $$ce of
            VarElim y -> $$(next cx done
                              (\cx' -> skip [|| ($$cx', VarElim y) ||])
                              (\ctev cx' -> [||
                                    let (TEV z ev) = $$ctev in
                                    if z == y then $$(yield [|| ev ||] [|| ($$cx',VarElim y) ||]) else $$(skip [|| ($$cx',VarElim y) ||])
                                ||])
                            )
            Proj1Elim c -> undefined
            Proj2Elim c -> undefined
            LetElim e -> undefined
     ||]
    next' :: (Quote m) => forall w. Code m (s, ElimTerm) -> Code m w -> (Code m (s, ElimTerm) -> Code m w) -> (Code m Event -> Code m (s, ElimTerm) -> Code m w) -> Code m w
    next' cx done skip yield = [||
        let (x,e) = $$cx in
        case e of
            EUse c s -> if isNull s
                        then $$done
                        else $$(nextFromElim [|| x ||] [|| c ||] done
                                  (\cx'c' -> [|| let (x',c') = $$cx'c' in $$(skip [|| (x',EUse c' s) ||]) ||])
                                  (\cev cx'c' -> [|| let ev = $$cev in let (x',c') = $$cx'c' in $$(yield [|| ev ||] [|| (x',EUse c' (deriv s ev)) ||]) ||])
                                )
            EIntR n -> $$(yield [|| IntEv n ||] [|| (x,EEpsR) ||])
            EEpsR -> $$done
            ECatR e1 e2 -> $$(next' [|| (x,e1) ||]
                                (yield [|| CatPunc ||] [|| (x,e2) ||])
                                (\cx'e1' -> skip [|| let (x',e1') = $$cx'e1' in (x', ECatR e1' e2) ||])
                                (\cev cx'e1' -> yield [|| CatEvA $$cev ||] [|| let (x',e1') = $$cx'e1' in (x',ECatR e1' e2) ||])
                            )
            EInL e -> $$(yield [|| PlusPuncA ||] [|| (x,e) ||])
            EInR e -> $$(yield [|| PlusPuncB ||] [|| (x,e) ||])
            EPlusCase _ _ _ -> undefined
     ||]


denoteElimTerm :: (Quote m) => ElimTerm -> Stream m TaggedEvent -> Stream m Event
denoteElimTerm e (S sf) = S (denoteElimTerm' e sf)


semElim :: (Quote m) => Elim -> StreamFunc m s TaggedEvent -> StreamFunc m (s,RunState) Event
semElim (VarElim y) (SF i0 next) = SF [|| ($$i0,SUnit) ||] $
    \ciu done skip yield -> [||
        $$(next [||let (i,_) = $$ciu in i||] done (\i' -> skip [||($$i',SUnit)||]) (\ctev ci' ->
            [||
                let (TEV z ev) = $$ctev in
                if z == y then $$(yield [|| ev ||] [|| ($$ci',SUnit) ||]) else $$(skip [||($$ci',SUnit)||])
            ||]
        ))
    ||]

semElim (Proj1Elim c) s =
    let (SF cix0 nextC) = semElim c s in
    SF cix0 $ \cix done skip yield -> nextC cix done skip (\cev cix' ->
            [||
                case $$cev of
                    CatEvA ev -> $$(yield [||ev||] cix')
                    _ -> error ""
            ||]
        )

semElim (Proj2Elim c) s =
    let (SF cix0 nextC) = semElim c s in
    SF [||let (i0,x0) = $$cix0 in (i0,SInL x0)||] $ \cix done skip yield ->
        [||
            let (i,x) = $$cix in
            case x of
                SInL x -> $$(nextC [||(i,x)||] done
                                (\cix' -> skip [||let (i',x') = $$cix' in (i',SInL x')||])
                                (\cev cix' ->
                                    [||
                                        case $$cev of
                                            CatEvA _ -> $$(skip [||let (i',x') = $$cix' in (i',SInL x')||])
                                            CatPunc -> $$(skip [||let (i',x') = $$cix' in (i',SInR x')||])
                                    ||]

                                ))
                SInR x -> $$(nextC [||(i,x)||] done skip yield)
        ||]


semElim (LetElim e) s = semElimTerm e s

semElimTerm :: (Quote m) => ElimTerm -> StreamFunc m s TaggedEvent -> StreamFunc m (s,RunState) Event
semElimTerm (EUse c t) s =
    let (SF cix0 nextElim) = semElim c s in
    SF [||let (i0,x0) = $$cix0 in (i0,SPair x0 (STy t))||] $ \cixt done skip yield ->
    [||
        let (i,SPair x (STy t)) = $$cixt in
        if isNull t then $$done
        else $$(nextElim [|| (i,x) ||] done
                (\cix' -> [|| let (i',x') = $$cix' in $$(skip [|| (i',SPair x' (STy t)) ||]) ||])
                (\cev cix' -> [||
                    let ev = $$cev in
                    let (i',x') = $$cix' in
                    $$(yield [|| ev ||] [|| (i',SPair x' (STy (deriv t ev))) ||])
                 ||])
               )
    ||]

semElimTerm EEpsR (SF cx0 _) = SF [||($$cx0,SUnit)||] (\_ done _ _ -> done)
semElimTerm (EIntR n) (SF cx0 _) = SF [||($$cx0,SBool False)||] $
    \cxb done _ yield -> [||
        let (x,SBool b) = $$cxb in
        if b then $$done else $$(yield [|| IntEv n ||] [||(x,SBool True)||])
    ||]

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

semElimTerm _ _ = undefined

semElimTerm' :: (Quote m) => ElimTerm -> Stream m TaggedEvent -> Stream m Event
semElimTerm' e (S sf) = S (semElimTerm e sf)