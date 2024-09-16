module Types where
import Test.QuickCheck (Arbitrary (..))
import Test.QuickCheck.Gen(Gen,frequency, sized)

data Ty = TyEps | TyInt | TyCat Ty Ty | TyPlus Ty Ty | TyStar Ty deriving (Eq,Ord,Show)

instance Arbitrary Ty where
    arbitrary = sized go
        where
            go 0 = frequency [(1,return TyEps),(5,return TyInt)]
            go n = frequency [(2,TyCat <$> go (n `div` 2) <*> go (n `div` 2)), (1,TyPlus <$> go (n `div` 2) <*> go (n `div` 2)), (1, TyStar <$> go (n `div` 2))]

isNull :: Ty -> Bool
isNull TyEps = True
isNull TyInt = False
isNull (TyCat {}) = False
isNull (TyPlus {}) = False
isNull (TyStar {}) = False