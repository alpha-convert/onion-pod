module Events where

import Types

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