{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs, AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

module Typed.Hoas where
import Data.Void

import qualified Term as Raw
import Control.Monad.State (runState, evalState, MonadState (..))
import qualified Types as StreamTypes
import Data.Function ((&))
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Data.Constraint

data TypeRep c a where
    TVoid :: TypeRep c Void
    TInt :: TypeRep c Int
    TPair :: (c a, c b) => TypeRep c a -> TypeRep c b -> TypeRep c (a,b)
    TSum :: (c a, c b) => TypeRep c a -> TypeRep c b -> TypeRep c (Either a b)

class StreamTyped a where
    typeRep :: TypeRep StreamTyped a

streamTypeRep :: TypeRep c a -> StreamTypes.Ty
streamTypeRep TVoid = StreamTypes.TyEps
streamTypeRep TInt = StreamTypes.TyInt
streamTypeRep (TPair a b) = StreamTypes.TyCat (streamTypeRep a) (streamTypeRep b)
streamTypeRep (TSum a b) = StreamTypes.TyPlus (streamTypeRep a) (streamTypeRep b)

data ExTy where
    PackTy :: forall a. StreamTyped a => TypeRep StreamTyped a -> ExTy

unTypeRep :: StreamTypes.Ty -> ExTy
unTypeRep StreamTypes.TyEps = PackTy TVoid
unTypeRep StreamTypes.TyInt = PackTy TInt
unTypeRep (StreamTypes.TyCat s t) =
    unTypeRep s & \(PackTy u) ->
    unTypeRep t & \(PackTy v) ->
    PackTy (TPair u v)
unTypeRep (StreamTypes.TyPlus s t) =
    unTypeRep s & \(PackTy u) ->
    unTypeRep t & \(PackTy v) ->
    PackTy (TSum u v)
unTypeRep (StreamTypes.TyStar _) = error "HOAS branch does not yet support stars"

data Term v c a where
    EpsR :: Term v c Void
    -- FreeVar :: c a => String -> Term v c a
    BoundVar :: c a => v a -> Term v c a
    IntR :: Int -> Term v c Int
    CatR :: (c a, c b) => Term v c a -> Term v c b -> Term v c (a,b)
    CatL :: (c a, c b, c d) => Term v c (a,b) -> (v a -> v b -> Term v c d) -> Term v c d
    Inl :: (c a, c b) => Term v c a -> Term v c (Either a b)
    Inr :: (c a, c b) => Term v c b -> Term v c (Either a b)
    PlusCase :: (c a, c b, c d) => Term v c (Either a b) -> (v a -> Term v c d) -> (v b -> Term v c d) -> Term v c d
    Let :: (c a, c b) => Term v c a -> (v a -> Term v c b) -> Term v c b


instance StreamTyped Void where
    typeRep = TVoid

instance StreamTyped Int where
    typeRep = TInt

instance (StreamTyped a, StreamTyped b) => StreamTyped (a,b) where
    typeRep = TPair typeRep typeRep

instance (StreamTyped a, StreamTyped b) => StreamTyped (Either a b) where
    typeRep = TSum typeRep typeRep


reConstrain :: (forall a. c1 a :- c2 a) -> Term v c1 a -> Term v c2 a
reConstrain f e = undefined

{-
toTerm :: forall a v. StreamTyped a => Term v StreamTyped a -> Raw.Term
toTerm e = evalState (go e (typeRep @a)) 0
    where
        fresh :: forall m. MonadState Int m => m String
        fresh = do
            n <- get
            put (n + 1)
            return $ "_x" ++ show n

        go :: forall a m v. (MonadState Int m) => Term v StreamTyped a -> TypeRep StreamTyped a -> m Raw.Term
        go EpsR _ = return Raw.EpsR
        go (FreeVar x) tr = return (Raw.Var x (streamTypeRep tr))
        go (BoundVar x) tr = return (Raw.Var x (streamTypeRep tr))
        go (IntR n) _ = return (Raw.IntR n)
        go (CatR e1 e2) (TPair s t) = do
            e1' <- go e1 s
            e2' <- go e2 t
            return (Raw.CatR e1' e2')
        go (CatL (e :: Term v StreamTyped u) k) tr = do
            x <- fresh
            y <- fresh
            z <- fresh
            e' <- go e (typeRep @u)
            ek <- go (k (FreeVar x) (FreeVar y)) tr
            return (Raw.Let z (streamTypeRep (typeRep @u)) e' (Raw.CatL x y z ek))
        go (Inl e) (TSum s t) = do
            e' <- go e s
            return (Raw.InL e' (streamTypeRep t))
        go (Inr e) (TSum s t) = do
            e' <- go e t
            return (Raw.InR e' (streamTypeRep s))
        go (PlusCase (e :: Term v StreamTyped u) k k') tr = do
            x <- fresh
            y <- fresh
            z <- fresh
            e' <- go e (typeRep @u)
            ek <- go (k (FreeVar x)) tr
            ek' <- go (k' (FreeVar y)) tr
            return (Raw.Let z (streamTypeRep (typeRep @u)) e' (Raw.PlusCase z x ek y ek'))
        go (Let (e :: Term v StreamTyped u) k) tr = do
            let tr' = typeRep @u
            x <- fresh
            e' <- go e tr'
            ek <- go (k (FreeVar x)) tr
            return (Raw.Let x (streamTypeRep tr') e' ek)

data TypedTerm where
    Pack :: forall a. StreamTyped a => TypeRep StreamTyped a -> (forall v. Term v StreamTyped a) -> TypedTerm

fromTerm :: Raw.Term -> M.Map String StreamTypes.Ty -> StreamTypes.Ty -> TypedTerm
fromTerm e m t = 
    unTypeRep t & \(PackTy tr) ->
        go e (M.mapWithKey varUp m) tr & \(e :: Term v StreamTyped a) ->
            Pack tr e
    where
        -- The "typed term" that is just this variable
        varUp :: String -> StreamTypes.Ty -> TypedTerm
        varUp x t =
            unTypeRep t & \(PackTy tr) ->
                Pack tr (FreeVar x)
        go :: StreamTyped a => Raw.Term -> M.Map String TypedTerm -> TypeRep StreamTyped a -> Term v StreamTyped a
        go Raw.EpsR _ TVoid = EpsR
        go Raw.EpsR _ _ = error ""
        go (Raw.IntR n) _ TInt = IntR n
        go (Raw.IntR {}) _ _ = error ""
        go (Raw.Var x _) _ (_ :: TypeRep StreamTyped a) = FreeVar @StreamTyped @a x
        go (Raw.CatR e1 e2) m (TPair s t) = CatR (go e1 m s) (go e2 m t)
        go (Raw.CatR e1 e2) m _ = error ""
        go (Raw.CatL x y z e) m t' =
            fromJust (M.lookup z m) & \(Pack (TPair s t) ez) ->
            CatL ez (\e1 e2 -> go e (M.insert x (Pack s e1) (M.insert y (Pack t e2) m)) t')
        go (Raw.Let x s e1 e2) m tr =
            unTypeRep s & \(PackTy trs) ->
            go e2 (M.insert x (Pack trs (go e1 m trs)) m) tr
        go (Raw.InL e _) m (TSum s t) = Inl (go e m s)
        go (Raw.InL {}) _ _ = error ""
        go (Raw.InR e _) m (TSum s t) = Inr (go e m t)
        go (Raw.InR {}) _ _ = error ""
        go (Raw.PlusCase z x e1 y e2) m tr =
            fromJust (M.lookup z m) & \(Pack (TSum s t) ez) ->
            PlusCase ez (\e -> go e1 (M.insert x (Pack s e) m) tr) (\e -> go e2 (M.insert y (Pack t e) m) tr)
        go (Raw.Nil _) _ _ = error "Unimplemented"
        go (Raw.Cons {}) _ _ = error "Unimplemented"
        go (Raw.StarCase {}) _ _ = error "Unimplemented"
        go (Raw.Fix {}) _ _ = error "Unimplemented"
        go (Raw.Rec {}) _ _ = error "Unimplemented"

-- fromTerm (Raw.IntR n) = _
-- fromTerm (CatL x y z e) = _
-- fromTerm (CatR e e') = _
-}