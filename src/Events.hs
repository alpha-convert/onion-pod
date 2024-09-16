module Events where

import Types
import Test.QuickCheck.Gen (Gen)
import Test.QuickCheck

data Event = IntEv Int | CatEvA Event | CatPunc | PlusPuncA | PlusPuncB deriving (Eq,Ord,Show)

data TaggedEvent = TEV String Event deriving (Eq,Ord,Show)

deriv :: Ty -> Event -> Ty
deriv TyEps _ = error ""
deriv TyInt (IntEv _) = TyEps
deriv TyInt _ = error ""
deriv (TyCat s t) (CatEvA ev) = TyCat (deriv s ev) t
deriv (TyCat _ t) CatPunc = t
deriv (TyCat {}) _ = error ""
deriv (TyPlus s _) PlusPuncA = s
deriv (TyPlus _ t) PlusPuncB = t
deriv (TyPlus {}) _ = error ""
deriv (TyStar _) PlusPuncA = TyEps
deriv (TyStar s) PlusPuncB = TyCat s (TyStar s)
deriv (TyStar {}) _ = error ""

genEventOfNonNullTy :: Ty -> Gen Event
genEventOfNonNullTy TyEps = error ""
genEventOfNonNullTy TyInt = IntEv <$> arbitrary
genEventOfNonNullTy (TyCat s _) = if isNull s then return CatPunc else CatEvA <$> genEventOfNonNullTy s
genEventOfNonNullTy (TyPlus _ _) = frequency [(1, return PlusPuncA),(1,return PlusPuncB)]
genEventOfNonNullTy (TyStar _) = sized $ \n -> frequency [(1, return PlusPuncA),(n,return PlusPuncB)]

genEventSeqOfTy :: Ty -> Gen [Event]
genEventSeqOfTy s = if isNull s then return [] else do
    ev <- genEventOfNonNullTy s
    evs <- genEventSeqOfTy (deriv s ev)
    return (ev : evs)

genTaggedEventsForContext :: [(String,Ty)] -> Gen [TaggedEvent]
genTaggedEventsForContext [] = return []
genTaggedEventsForContext ((x,t):g) = do
    tevs <- go x t
    tevs' <- genTaggedEventsForContext g
    return (tevs ++ tevs')
    where
        go x t = fmap (TEV x) <$> genEventSeqOfTy t