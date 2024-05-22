module Types where

data Ty = TyEps | TyInt | TyCat Ty Ty | TyPlus Ty Ty | TyStar Ty deriving (Eq,Ord,Show)

isNull :: Ty -> Bool
isNull TyEps = True
isNull TyInt = False
isNull (TyCat {}) = False
isNull (TyPlus {}) = False
isNull (TyStar {}) = False