{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs, AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module PHoas where
import Data.Void

import qualified Term as Raw
import Control.Monad.State (runState, evalState, MonadState (..))
import qualified Types as StreamTypes
import Data.Function ((&))
import qualified Data.Map as M
import Data.Maybe (fromJust)

data TypeRep c a where
    TVoid :: TypeRep c Void
    TInt :: TypeRep c Int
    TPair :: (c a, c b) => TypeRep c a -> TypeRep c b -> TypeRep c (a,b)
    TSum :: (c a, c b) => TypeRep c a -> TypeRep c b -> TypeRep c (Either a b)

class StreamTyped a where
    typeRep :: TypeRep StreamTyped a
    streamTypeRep :: StreamTypes.Ty

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

data Term c a where
    EpsR :: Term c Void
    Var :: c a => String -> Term c a
    IntR :: Int -> Term c Int
    CatR :: (c a, c b) => Term c a -> Term c b -> Term c (a,b)
    CatL :: (c a, c b, c d) => Term c (a,b) -> (Term c a -> Term c b -> Term c d) -> Term c d
    Inl :: (c a, c b) => Term c a -> Term c (Either a b)
    Inr :: (c a, c b) => Term c b -> Term c (Either a b)
    PlusCase :: (c a, c b, c d) => Term c (Either a b) -> (Term c a -> Term c d) -> (Term c b -> Term c d) -> Term c d
    Let :: (c a, c b) => Term c a -> (Term c a -> Term c b) -> Term c b


instance StreamTyped Void where
    typeRep = TVoid
    streamTypeRep = StreamTypes.TyEps

instance StreamTyped Int where
    typeRep = TInt
    streamTypeRep = StreamTypes.TyInt

instance (StreamTyped a, StreamTyped b) => StreamTyped (a,b) where
    typeRep = TPair typeRep typeRep
    streamTypeRep = StreamTypes.TyCat (streamTypeRep @a) (streamTypeRep @b)

instance (StreamTyped a, StreamTyped b) => StreamTyped (Either a b) where
    typeRep = TSum typeRep typeRep
    streamTypeRep = StreamTypes.TyPlus (streamTypeRep @a) (streamTypeRep @b)


with :: forall v c r. (forall a. c a => r a) -> (c v => r v)
with x = x

toTerm :: forall c a. (c a, forall r. c r => StreamTyped r) => Term c a -> Raw.Term
toTerm e = evalState (go e) 0
    where
        fresh :: forall m. MonadState Int m => m String
        fresh = do
            n <- get
            put (n + 1)
            return $ "_x" ++ show n

        go :: forall c a m . (c a, forall r. c r => StreamTyped r, MonadState Int m) => Term c a -> m Raw.Term
        go EpsR = return Raw.EpsR
        go (Var x) = return (Raw.Var x (streamTypeRep @a))
        go (IntR n) = return (Raw.IntR n)
        go (CatR e1 e2) = do
            e1' <- go e1
            e2' <- go e2
            return (Raw.CatR e1' e2')
        go (CatL e k) = do
            e' <- go e
            x <- fresh
            y <- fresh
            _
        go (Inl e) = _
        go (Inr e) = _
        go (PlusCase e k k') = _
        go (Let e k) = _

data TypedTerm where
    Pack :: forall a. StreamTyped a => TypeRep StreamTyped a -> Term StreamTyped a -> TypedTerm

fromTerm :: Raw.Term -> M.Map String StreamTypes.Ty -> StreamTypes.Ty -> TypedTerm
fromTerm e m t = 
    unTypeRep t & \(PackTy tr) ->
    go e (M.mapWithKey _ m) tr & \(e :: Term StreamTyped a) ->
    Pack tr e
    where
        go :: StreamTyped a => Raw.Term -> M.Map String TypedTerm -> TypeRep StreamTyped a -> Term StreamTyped a
        go Raw.EpsR _ TVoid = EpsR
        go Raw.EpsR _ _ = error ""
        go (Raw.IntR n) _ TInt = IntR n
        go (Raw.IntR {}) _ _ = error ""
        go (Raw.Var x _) _ (_ :: TypeRep StreamTyped a) = Var @StreamTyped @a x
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