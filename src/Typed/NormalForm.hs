{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Typed.NormalForm where

import Types
import Typed.Hoas
import Data.Void
import Control.Monad (join, liftM2)

class Base a where
    embBase :: a -> Term v Rf a
instance Base Int where
    embBase = IntR

data Ne v a where
    -- NFreeVar :: String -> Ne v a
    NBoundVar :: v a -> Ne v a

data Nf (v :: * -> *) a where
    NUp :: Base a => Ne v a -> Nf v a
    NLift :: Base a => a -> Nf v a
    NEpsR :: Nf v Void
    NCatR :: (Rf a, Rf b) => Nf v a -> Nf v b -> Nf v (a,b)
    NCatL :: (Rf a, Rf b) => Ne v (a,b) -> (v a -> v b -> Nf v c) -> Nf v c
    NPlusCase :: (Rf a, Rf b) => Ne v (Either a b) -> (v a -> Nf v c) -> (v b -> Nf v c) -> Nf v c
    NInl :: (Rf a, Rf b) => Nf v a -> Nf v (Either a b)
    NInr :: (Rf a, Rf b) => Nf v b -> Nf v (Either a b)

embNe :: Rf a => Ne v a -> Term v Rf a
-- embNe (NFreeVar x) = FreeVar x
embNe (NBoundVar x) = BoundVar x

embNf :: Rf a => Nf v a -> Term v Rf a
embNf (NUp ne) = embNe ne
embNf (NLift x) = embBase x
embNf NEpsR = EpsR
embNf (NCatR e e') = CatR (embNf e) (embNf e')
embNf (NCatL ne k) = CatL (embNe ne) (\e e' -> embNf (k e e'))
embNf (NPlusCase ne k k') = PlusCase (embNe ne) (embNf . k) (embNf . k')
embNf (NInl e) = Inl (embNf e)
embNf (NInr e) = Inr (embNf e)

data Cover (v :: * -> *) a where
    Leaf :: a -> Cover v a
    Spread :: (Rf a, Rf b) => Ne v (a,b) -> (v a -> v b -> Cover v c) -> Cover v c
    Branch :: (Rf a, Rf b) => Ne v (Either a b) -> (v a -> Cover v c) -> (v b -> Cover v c) -> Cover v c

instance Functor (Cover v) where
    fmap f x = x >>= Leaf . f

instance Applicative (Cover v) where
    pure = return
    liftA2 = liftM2

instance Monad (Cover v) where
    return = Leaf
    (Leaf x) >>= f = f x
    (Spread ne k) >>= f = Spread ne (\e e' -> k e e' >>= f)
    (Branch ne k k') >>= f = Branch ne ((>>= f) . k) ((>>= f) . k')

type family Sem (v :: * -> *) a where
    Sem v Void = ()
    Sem v Int = Cover v (Either Int (Ne v Int))
    Sem v (a,b) = Cover v (Sem v a, Sem v b)
    Sem v (Either a b) = Cover v (Either (Sem v a) (Sem v b))

class StreamTyped a => Rf a where
    reify :: Sem v a -> Nf v a
    reflect :: forall v. Ne v a -> Sem v a
    reflectBoundVar :: v a -> Sem v a


quote :: forall v a. Rf a => Sem v a -> Term v Rf a
quote = embNf . (reify @a)

instance Rf Void where
    reify _ = NEpsR
    reflect _ = ()
    reflectBoundVar _ = ()

instance Rf Int where
    reify (Leaf (Left n)) = NLift n
    reify (Leaf (Right ne)) = NUp ne
    reify (Spread ne k) = NCatL ne (\e e' -> reify (k e e'))
    reify (Branch ne k k') = NPlusCase ne (reify . k) (reify . k')
    reflect ne = Leaf (Right ne)
    reflectBoundVar v = Leaf (Right (NBoundVar v))

instance (Rf a, Rf b) => Rf (a,b) where
    reify (Leaf (sa,sb)) = NCatR (reify sa) (reify sb)
    reify (Spread ne k) = NCatL ne (\e e' -> reify (k e e'))
    reify (Branch ne k k') = NPlusCase ne (reify . k) (reify . k')
    reflect ne = Spread ne (\va vb -> Leaf (reflectBoundVar va,reflectBoundVar vb))
    reflectBoundVar v = Spread (NBoundVar v) (\va vb -> Leaf (reflectBoundVar va,reflectBoundVar vb))

instance (Rf a, Rf b) => Rf (Either a b) where
    reify (Leaf (Left x)) = NInl (reify x)
    reify (Leaf (Right x)) = NInr (reify x)
    reify (Spread ne k) = NCatL ne (\e e' -> reify (k e e'))
    reify (Branch ne k k') = NPlusCase ne (reify . k) (reify . k')
    reflect ne = Branch ne (Leaf . Left . reflectBoundVar) (Leaf . Right . reflectBoundVar)
    reflectBoundVar v = Branch (NBoundVar v) (Leaf . Left . reflectBoundVar) (Leaf . Right . reflectBoundVar)

runCover :: forall v a . Rf a => Cover v (Sem v a) -> Sem v a
runCover = go (typeRep @a)
    where
        go :: forall a c. TypeRep c a -> Cover v (Sem v a) -> Sem v a
        go TVoid _ = ()
        go TInt c = join c
        go (TPair _ _) c = join c
        go (TSum _ _) c = join c

eval :: forall v a. Rf a => Term v Rf a -> Sem v a
eval EpsR = ()
-- eval (FreeVar x) = reflect @a @v (NFreeVar x)
eval (BoundVar v) = reflectBoundVar v
eval (IntR n) = Leaf (Left n)
eval (CatR e1 e2) = Leaf (eval e1, eval e2)
eval (CatL e k) = runCover @v @a $ do
    (sa,sb) <- eval e
    return (eval (k (quote sa) (quote sb)))
eval (Inl e) = Leaf (Left (eval e))
eval (Inr e) = Leaf (Right (eval e))
eval (PlusCase e k k') = runCover @v @a $ do
    u <- eval e
    return $ case u of
        Left sa -> eval (k (quote sa))
        Right sb -> eval (k' (quote sb))
eval (Let e k) = eval (k e)

normalize :: Rf a => Term v Rf a -> Term v Rf a
normalize = quote . eval