{-# LANGUAGE ViewPatterns, LambdaCase, LinearTypes, TypeFamilies #-}
module Random where


import Data.Map as M
import Data.Maybe

data Term a where
    --   TmVar String
    -- | TmLet String Term Term
    TmVal :: Val a -> Term a
    TmPair :: Term a -> Term b -> Term (a,b)
    TmProj1 :: Term (a,b) -> Term a
    TmProj2 :: Term (a,b) -> Term b

data Val a where
    ValInt :: Int -> Val Int
    ValPair :: Val a -> Val b -> Val (a,b)

data Step s a where
    Yield :: a -> Step s a
    Skip :: s -> Step s a

data SF s a where
    SFInt :: (s -> Step s Int) -> SF s Int
    SFPair :: SF s a -> SF s b -> SF s (a,b)
    
data Pull a where
    Pull :: forall a s. s -> SF s a -> Pull a

data Lens s s' = Lens {put :: s -> s' -> s', get :: s' -> s}

proj1L :: Lens a (a,b)
proj1L = Lens (\a (_,b) -> (a,b)) fst

proj2L :: Lens b (a,b)
proj2L = Lens (\b (a,_) -> (a,b)) snd

lensSF :: Lens s s' -> SF s a -> SF s' a
lensSF l (SFInt f) = SFInt $ \s' -> case f (get l s') of
                                            Skip s -> Skip (put l s s')
                                            Yield a -> Yield a
lensSF l (SFPair sf1 sf2) = SFPair (lensSF l sf1) (lensSF l sf2)

denoteVal :: Val a -> SF () a
denoteVal (ValInt n) = SFInt (const (Yield n))
denoteVal (ValPair v1 v2) = SFPair (denoteVal v1) (denoteVal v2)

denote :: Term a -> Pull a
denote (TmVal v) = Pull () (denoteVal v)
denote (TmPair e1 e2) =
    case (denote e1, denote e2) of
        (Pull x0 sf1, Pull x1 sf2) -> Pull (x0,x1) (SFPair (lensSF proj1L sf1) (lensSF proj2L sf2))
denote (TmProj1 e) = 
    case denote e of
        Pull x0 (SFPair sf _) -> Pull x0 sf
denote (TmProj2 e) = 
    case denote e of
        Pull x0 (SFPair _ sf) -> Pull x0 sf

-- denote :: M.Map String (Pull Val) -> Term -> Pull Val
-- denote eta (TmVar x) = fromMaybe (error "") (M.lookup x eta)
-- denote eta (TmLet x e e') = denote (M.insert x (denote eta e) eta) e'
-- -- denote eta (TmVal v) = S (SF () (const (Yield v)))
-- -- denote eta (TmPair (denote eta -> (S (SF x0 f0))) (denote eta -> (S (SF x1 f1)))) =
--     -- S $ SF (Left x0, Left x1) $
--         -- \case (Left (f0 -> Skip x0'),s1) -> Skip (Left x0,s1)
--             --   (Left (f0 -> Yield v0),s1) -> Skip (Right v0,s1)
--             --   (Right v0,Left (f1 -> Skip x1')) -> Skip (Right v0, Left x1')
--             --   (Right v0,Left (f1 -> Yield v1)) -> Yield (ValPair v0 v1)
-- denote eta (TmProj1 e) = fmap (\(ValPair v _) -> v) (denote eta e)
-- denote eta (TmProj2 e) = fmap (\(ValPair _ v) -> v) (denote eta e)