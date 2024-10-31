{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
module PHoas where
import Data.Void

import qualified Term as Raw

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