{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
module NormalForm where

import Types
import PHoas
import Data.Void

class Base a where

instance Base Int

data VNe v s s' where
    NVar :: v s -> VNe v s Void
    NInt :: Int -> VNe v Int Void
    NCatPunc :: VNe v (Void,s) s
    NCatEvA :: VNe v s s' -> VNe v (s,t) (s',t)
    NPlusPuncA :: VNe v (Either s t) s
    NPlusPuncB :: VNe v (Either s t) t

data VNf v a where
    NDone :: VNf v Void
    NSendThen :: VNe v a a' -> VNf v a' -> VNf v a
    NCase :: VNe v (Either a b) s -> (v a -> VNf v c) -> (v b -> VNf v c) -> VNf v c

data Nf a where
    NF :: (forall v. VNf v a) -> Nf a

catR :: VNf v a -> VNf v b -> VNf v (a,b)
catR NDone nf = NSendThen NCatPunc nf
catR (NSendThen ne nf) nf' = NSendThen (NCatEvA ne) (catR nf nf')
catR (NCase b k k') nf' = NCase b (\vs -> catR (k vs) nf') (\vs -> catR (k' vs) nf')

plusCase :: v (Either a b) -> (v a -> VTerm v c) -> (v b -> VTerm v c) -> VNf v c
plusCase = _

nLet :: VNf v a -> (v a -> VTerm v b) -> VNf v b
nLet = _

normalize :: Term a -> Nf a
normalize (T e) = NF (go e)
    where
        go :: VTerm v a -> VNf v a
        go EpsR = NDone
        go (Var x) = NSendThen (NVar x) NDone
        go (IntR n) = NSendThen (NInt n) NDone
        go (CatR e e') = catR (go e) (go e')
        go (PlusCase v f g) = plusCase v f g
        go (InL e) = NSendThen NPlusPuncA (go e)
        go (InR e) = NSendThen NPlusPuncB (go e)
        go (Let e k) = nLet (go e) k

