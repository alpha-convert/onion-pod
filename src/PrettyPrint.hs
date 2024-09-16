{-# LANGUAGE  TypeSynonymInstances, FlexibleInstances  #-}
module PrettyPrint where

class PrettyPrint a where
    pp :: a -> String

instance PrettyPrint String where
    pp = id