{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
module PHoas where
import Data.Void

import qualified Term as Raw

data VTerm v a where
    EpsR :: VTerm v Void
    Var :: v a -> VTerm v a
    IntR :: Int -> VTerm v Int
    CatR :: VTerm v a -> VTerm v b -> VTerm v (a,b)
    CatL :: v (a,b) -> (v a -> v b -> VTerm v a) -> VTerm v a
    InL :: VTerm v a -> VTerm v (Either a b)
    InR :: VTerm v b -> VTerm v (Either a b)
    PlusCase :: v (Either a b) -> (v a -> VTerm v c) -> (v b -> VTerm v c) -> VTerm v c
    Let :: VTerm v a -> (v a -> VTerm v b) -> VTerm v b

data Term a where
  T :: (forall v. VTerm v a) -> Term a