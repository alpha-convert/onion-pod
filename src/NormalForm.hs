{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module NormalForm where

import Types
import PHoas
import Data.Void
import Control.Monad (join, liftM2)

class Base a where
    embBase :: a -> Term Rf a
instance Base Int where
    embBase = IntR

data Ne a where
    NVar :: String -> Ne a

data Nf a where
    NUp :: Base a => Ne a -> Nf a
    NLift :: Base a => a -> Nf a
    NEpsR :: Nf Void
    NCatR :: (Rf a, Rf b) => Nf a -> Nf b -> Nf (a,b)
    NCatL :: (Rf a, Rf b) => Ne (a,b) -> (Term Rf a -> Term Rf b -> Nf c) -> Nf c
    NPlusCase :: (Rf a, Rf b) => Ne (Either a b) -> (Term Rf a -> Nf c) -> (Term Rf b -> Nf c) -> Nf c
    NInl :: (Rf a, Rf b) => Nf a -> Nf (Either a b)
    NInr :: (Rf a, Rf b) => Nf b -> Nf (Either a b)

embNe :: Rf a => Ne a -> Term Rf a
embNe (NVar x) = Var x

embNf :: Rf a => Nf a -> Term Rf a
embNf (NUp ne) = embNe ne
embNf (NLift x) = embBase x
embNf NEpsR = EpsR
embNf (NCatR e e') = CatR (embNf e) (embNf e')
embNf (NCatL ne k) = CatL (embNe ne) (\e e' -> embNf (k e e'))
embNf (NPlusCase ne k k') = PlusCase (embNe ne) (embNf . k) (embNf . k')
embNf (NInl e) = Inl (embNf e)
embNf (NInr e) = Inr (embNf e)


data Cover a where
    Leaf :: a -> Cover a
    Spread :: (Rf a, Rf b) => Ne (a,b) -> (Term Rf a -> Term Rf b -> Cover c) -> Cover c
    Branch :: (Rf a, Rf b) => Ne (Either a b) -> (Term Rf a -> Cover c) -> (Term Rf b -> Cover c) -> Cover c

instance Functor Cover where
    fmap f x = x >>= Leaf . f

instance Applicative Cover where
    pure = return
    liftA2 = liftM2

instance Monad Cover where
    return = Leaf
    (Leaf x) >>= f = f x
    (Spread ne k) >>= f = Spread ne (\e e' -> k e e' >>= f)
    (Branch ne k k') >>= f = Branch ne ((>>= f) . k) ((>>= f) . k')


type family Sem a where
    Sem Void = ()
    Sem Int = Cover (Either Int (Ne Int))
    Sem (a,b) = Cover (Sem a, Sem b)
    Sem (Either a b) = Cover (Either (Sem a) (Sem b))

class StreamTyped a => Rf a where
    reify :: Sem a -> Nf a
    reflect :: Ne a -> Sem a


quote :: forall a. Rf a => Sem a -> Term Rf a
quote = embNf . (reify @a)

instance Rf Void where
    reify _ = NEpsR
    reflect _ = ()

instance Rf Int where
    reify (Leaf (Left n)) = NLift n
    reify (Leaf (Right ne)) = NUp ne
    reify (Spread ne k) = NCatL ne (\e e' -> reify (k e e'))
    reify (Branch ne k k') = NPlusCase ne (reify . k) (reify . k')
    reflect ne = Leaf (Right ne)

instance (Rf a, Rf b) => Rf (a,b) where
    reify (Leaf (sa,sb)) = NCatR (reify sa) (reify sb)
    reify (Spread ne k) = NCatL ne (\e e' -> reify (k e e'))
    reify (Branch ne k k') = NPlusCase ne (reify . k) (reify . k')
    reflect ne = Spread ne (\e e' -> Leaf (eval e, eval e'))

instance (Rf a, Rf b) => Rf (Either a b) where
    reify (Leaf (Left x)) = NInl (reify x)
    reify (Leaf (Right x)) = NInr (reify x)
    reify (Spread ne k) = NCatL ne (\e e' -> reify (k e e'))
    reify (Branch ne k k') = NPlusCase ne (reify . k) (reify . k')
    reflect ne = Branch ne (Leaf . Left . eval) (Leaf . Right . eval)

runCover :: forall a . Rf a => Cover (Sem a) -> Sem a
runCover = go (typeRep @a)
    where
        go :: forall a c. TypeRep c a -> Cover (Sem a) -> Sem a
        go TVoid _ = ()
        go TInt c = join c
        go (TPair _ _) c = join c
        go (TSum _ _) c = join c

eval :: forall a. Rf a => Term Rf a -> Sem a
eval EpsR = ()
eval (Var x) = reflect @a (NVar x)
eval (IntR n) = Leaf (Left n)
eval (CatR e1 e2) = Leaf (eval e1, eval e2)
eval (CatL e k) = runCover @a $ do
    (sa,sb) <- eval e
    return (eval (k (quote sa) (quote sb)))
eval (Inl e) = Leaf (Left (eval e))
eval (Inr e) = Leaf (Right (eval e))
eval (PlusCase e k k') = runCover @a $ do
    u <- eval e
    return $ case u of
        Left sa -> eval (k (quote sa))
        Right sb -> eval (k' (quote sb))
eval (Let e k) = eval (k e)

normalize :: Rf a => Term Rf a -> Term Rf a
normalize = quote . eval