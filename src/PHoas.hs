
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs, AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
module PHoas where
import Data.Void

import qualified Term as Raw
import Control.Monad.State (runState, evalState, MonadState (..))
import qualified Types as StreamTypes
import Data.Function ((&))
import qualified Data.Map as M
{-
data TypeRep a where
    TVoid :: TypeRep Void
    TInt :: TypeRep Int
    TPair :: TypeRep a -> TypeRep b -> TypeRep (a,b)
    TSum :: TypeRep a -> TypeRep b -> TypeRep (Either a b)

class StreamTyped a where
    typeRep :: TypeRep a
    streamTypeRep :: StreamTypes.Ty

data ExTy where
    PackTy :: forall a. StreamTyped a => TypeRep a -> ExTy

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
    Pack :: forall a. StreamTyped a => Term StreamTyped a -> TypedTerm

fromTerm :: Raw.Term -> M.Map String StreamTypes.Ty -> Maybe TypedTerm
fromTerm e m = go e (unTypeRep <$> m)
    where
        go :: Raw.Term -> M.Map String ExTy -> Maybe TypedTerm
        go Raw.EpsR _ = return (Pack EpsR)
        go (Raw.IntR n) _ = _
        go (Raw.Var x s) _ = unTypeRep s & \(PackTy (_ :: TypeRep a)) -> return (Pack (Var @StreamTyped @a x))
        go (Raw.CatR e1 e2) m = do 
            Pack e1' <- go e1 m
            Pack e2' <- go e1 m
            return (Pack (CatR e1' e2'))
            -- CatR <$> (go e m) <*> (go e' m)
        go (Raw.CatL x y z e) m = do
            (PackTy (TPair (s :: TypeRep a) (t :: TypeRep b))) <- M.lookup z m

            _
            return (Pack $ CatL @StreamTyped (Var @StreamTyped @(a,b) z) (\e e' -> _))
        go (Raw.Let x e e') m = _
        go (Raw.InL e) m = do
            Pack e' <- go e m
            return _
        go (Raw.InR e) m = _
        go (Raw.PlusCase z x e1 y e2) m = _

        go Raw.Nil _ = error "Unimplemented"
        go (Raw.Cons {}) _ = error "Unimplemented"
        go (Raw.StarCase {}) _ = error "Unimplemented"
        go (Raw.Fix {}) _ = error "Unimplemented"
        go (Raw.Rec {}) _ = error "Unimplemented"
-- fromTerm (Raw.IntR n) = _
-- fromTerm (CatL x y z e) = _
-- fromTerm (CatR e e') = _
-}