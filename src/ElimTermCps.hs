{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
module ElimTermCps where

import Events
import Types
import Term
import qualified Data.Map as Map
import StreamCps
import Data.IntMap (partition)


{- Are Elims just a focusing thing? -}
data Elim = VarElim String
        --   | HistVarElim String
          | Proj1Elim Elim
          | Proj2Elim Elim
          | LetElim ElimTerm

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
                Just ev -> error $ "Unexpected event in elimderiv"
         )
        go (Proj2Elim el) ev k = go el ev (\el' ev ->
            case ev of
                Nothing -> k (Proj2Elim el') Nothing
                Just (CatEvA _) -> k (Proj2Elim el') Nothing
                Just CatPunc -> k el' Nothing
                Just ev -> error $ "Unexpected event in elimderiv"
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