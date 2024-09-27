
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell #-}

module PullSemCPSStaged where
import ElimTerm
import StreamCPSStaged
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
    -- nextFromElim x' (VarElim y) done skip yield = 
    --     next x' 
    --         done 
    --         (\x'' -> skip (x'', VarElim y))
    --         (\(TEV z ev) x'' -> if z == y 
    --                             then yield ev (x'', VarElim y) 
    --                             else skip (x'', VarElim y))
    -- nextFromElim x' (Proj1Elim c) done skip yield = 
    --     nextFromElim x' c
    --         done
    --         (\(x'', c') -> skip (x'', Proj1Elim c'))
    --         (\ev (x'', c') -> case ev of
    --             CatEvA ev' -> yield ev' (x'', Proj1Elim c')
    --             _ -> error "Unexpected event in Proj1Elim."
    --         )

    -- nextFromElim x' (Proj2Elim c) done skip _ = 
    --     nextFromElim x' c
    --         done
    --         (\(x'', c') -> skip (x'', Proj2Elim c'))
    --         (\ev (x'', c') -> case ev of
    --             CatEvA _ -> skip (x'', Proj2Elim c')
    --             CatPunc -> skip (x'', c')
    --             _ -> error "Unexpected event in Proj2Elim."
    --         )
    -- nextFromElim x' (LetElim e') done skip yield = 
    --     next' (x', e') 
    --         done
    --         (\(x'', e'') -> skip (x'', LetElim e''))
    --         (\ev (x'', e'') -> yield ev (x'', LetElim e''))

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
            -- ECatR e1 e2 -> $$(next' [|| (x,e1) ||]
                                -- (yield [|| CatPunc ||] [|| (x,e2) ||])
                                -- (\cx'e1' -> skip [|| let (x',e1') = $$cx'e1' in (x', ECatR e1' e2) ||])
                                -- (\cev cx'e1' -> yield [|| CatEvA $$cev ||] [|| let (x',e1') = $$cx'e1' in (x',ECatR e1' e2) ||])
                            -- )
            EInL e -> $$(yield [|| PlusPuncA ||] [|| (x,e) ||])
            EInR e -> $$(yield [|| PlusPuncB ||] [|| (x,e) ||])
            EPlusCase _ _ _ -> undefined
     ||]

    -- next' (x', ECatR e1 e2) _ skip yield =
    --     next' (x', e1)
    --         (yield CatPunc (x', e2))
    --         (\(x'', e1') -> skip (x'', ECatR e1' e2))
    --         --- Wrap the event in a CatEvA term so we know what part
    --         --- of the stream it belongs to.
    --         (\ev (x'', e1') -> yield (CatEvA ev) (x'', ECatR e1' e2))

    -- next' (x', EInL e') _ _ yield = yield PlusPuncA (x', e')
    -- next' (x', EInR e') _ _ yield = yield PlusPuncB (x', e')

    -- next' (x', EPlusCase c e1 e2) done skip _ =
    --     nextFromElim x' c
    --         done
    --         (\(x'', c') -> skip (x'', EPlusCase c' e1 e2))
    --         (\ev (x'', _) -> case ev of
    --             PlusPuncA -> skip (x'', e1)
    --             PlusPuncB -> skip (x'', e2)
    --             _ -> error "Unexpected event in PlusCase."
    --         )
    
    -- next' (_, EFix _) _ _ _ = error "Not yet implemented."
    -- next' (_, ERec) _ _ _ = error "We don't know how to do this yet."

denoteElimTerm :: (Quote m) => ElimTerm -> Stream m TaggedEvent -> Stream m Event
denoteElimTerm e (S sf) = S (denoteElimTerm' e sf)