{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveLift #-}
module ElimTerm where

import Events
import Types
import Term
import qualified Data.Map as Map
import Language.Haskell.TH.Syntax
import GHC.Real (underflowError)

{- Are Elims just a focusing thing? -}
data Elim where
  VarElim :: String -> Elim
  Proj1Elim :: Elim -> Elim
  Proj2Elim :: Elim -> Elim
  LetElim :: ElimTerm -> Elim
  deriving (Eq, Ord, Show, Lift)

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
                Just ev -> error $ "Unexpected event " ++ show ev ++ " in elimderiv"
         )
        go (Proj2Elim el) ev k = go el ev (\el' ev ->
            case ev of
                Nothing -> k (Proj2Elim el') Nothing
                Just (CatEvA _) -> k (Proj2Elim el') Nothing
                Just CatPunc -> k el' Nothing
                Just ev -> error $ "Unexpected event " ++ show ev ++ " in elimderiv"
         )
        -- UHH no idea.
        go (LetElim e) ev k = k (LetElim e) (Just ev)


data ElimTerm where
  EEpsR :: ElimTerm
  EUse :: Elim -> Ty -> ElimTerm
  EIntR :: Int -> ElimTerm
  ECatR :: ElimTerm -> ElimTerm -> ElimTerm
  EInR :: ElimTerm -> ElimTerm
  EInL :: ElimTerm -> ElimTerm
  EPlusCase :: Elim -> ElimTerm -> ElimTerm -> ElimTerm
  EFix :: ElimTerm -> ElimTerm
  ERec :: ElimTerm
  deriving (Eq, Ord, Show, Lift)

fixSubst :: ElimTerm -> ElimTerm -> ElimTerm
fixSubst = undefined

-- subst e e' x = e[e'/x]
{-
FIXME: this should really be locally nameless. But not entirely clear how to do so. :)
-}
subst :: ElimTerm -> ElimTerm -> String -> ElimTerm
subst e e' x = go e
    where
        go EEpsR = EEpsR
        go (EUse el t) = EUse (goEl el) t
        go (EIntR n) = EIntR n
        go (ECatR e1 e2) = ECatR (go e1) (go e2)
        go (EInR e) = EInR (go e)
        go (EInL e) = EInL (go e)
        go (EPlusCase el e1 e2) = EPlusCase (goEl el) (go e1) (go e2)
        go (EFix e) = EFix e
        go ERec = ERec

        goEl (VarElim y) | x == y = LetElim e'
        goEl (VarElim y) | otherwise = VarElim y
        goEl (Proj1Elim el) = Proj1Elim (goEl el)
        goEl (Proj2Elim el) = Proj2Elim (goEl el)
        {- FIXME: hmm this seems like it might be a problem, we're probably capturing like crazy here...-}
        goEl (LetElim e) = LetElim (go e)


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
        go m (InL e _) = EInL (go m e)
        go m (InR e _) = EInR (go m e)
        go m (PlusCase z x e1 y e2) =
            let c = getElim m z in
            EPlusCase c (go (Map.insert x (delPi2 c) m) e1) (go (Map.insert y (delPi2 c) m) e2)
        go m (Nil _) = EInL EEpsR
        go m (Cons e1 e2) = EInR (ECatR (go m e1) (go m e2))
        go m (StarCase z e1 x xs e2) =
            let c = getElim m z in
            EPlusCase c (go m e1) (go (Map.insert x (Proj1Elim (delPi2 c)) (Map.insert xs (Proj2Elim (delPi2 c)) m)) e2)
        go m (Fix e') = EFix (go m e')
        go m Rec = ERec
        {-FIXME: Hmm. this might not work if nested inside a CatL.
            let (a;b) = e in
            (3::a;5::b).
            introduces two independent copies of e... doubles the computation.
            SHIT!
            We definitely want to share those.
        -}
        go m (Let x _ e e') = go (Map.insert x (LetElim (go m e)) m) e'

data RunState =
      SUnit
    | SBool Bool
    | SInL RunState
    | SInR RunState
    | SPair RunState RunState
    | STy Ty

{-

fix foo(xs : (s + t)*) s* || t* :=
    case xs of
       nil => nil
     | y::ys =>
        let u = foo(ys) in 
        let (as,bs) = u in
        case y of
            inl a => (a:as,bs)
-}