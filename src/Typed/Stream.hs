{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Typed.Stream where
import Data.Void (Void, absurd)
import Typed.Hoas
import Data.Function ((&), fix)

class Subsing a where
    ssdec :: Maybe ()

instance Subsing () where
    ssdec = Just ()

instance Subsing Void where
    ssdec = Nothing


data Cont a = C(forall w. (a -> w) -> w)

data family Stream s a

data instance Stream s Void = SV Void

data instance Stream s Int where
    SI :: forall s. (s -> Either s Int) -> Stream s Int

data EStep s = ESkip s | K1 s | K2 s

data instance Stream s (Either a b) where
    SS :: forall a b s.
        (s -> EStep s) ->
        Stream s a ->
        Stream s b ->
        Stream s (Either a b)
    S1 :: Stream s a -> Stream s (Either a b)
    S2 :: Stream s b -> Stream s (Either a b)

data instance Stream s (a,b) where
    SP :: forall a b s. Stream s a -> Stream s b -> Stream s (a,b)

data instance Stream s [a] where
    {- while/do -}
    SStar ::
        s' ->
        Stream (s,s') a ->
        (s' -> Maybe s') ->
        Stream s [a]

run :: forall a s. StreamTyped a => Stream s a -> s -> a
run s x0 = fst (go (typeRep @a) s x0)
    where
        go :: forall a s. TypeRep StreamTyped a -> Stream s a -> s -> (a,s)
        go TVoid (SV v) x0 = absurd v
        go TInt (SI f) x0 = flip fix x0 $ \r x -> case f x of
                                                    Left x' -> r x'
                                                    Right n -> (n,x) {-fixme: final state should be output -}
        go (TPair t t') (SP s s') x =
            go t s x & \(a,x') ->
            go t' s' x' & \(b,x'') ->
            ((a,b),x'')
        go (TSum t _) (S1 s) x = go t s x & \(a,x') -> (Left a, x')
        go (TSum _ t') (S2 s) x = go t' s x & \(b,x') -> (Right b, x')
        go (TSum t t') (SS init s s') x =
            case loop x of 
                Left x' -> go t s x' & \(a,x'') -> (Left a, x'')
                Right x' -> go t' s' x' & \(b,x'') -> (Right b, x'')
            where
                loop x = case init x of
                           ESkip x' -> loop x'
                           K1 x' -> Left x'
                           K2 x' -> Right x'


data Isom a b = I { to :: a -> b, from :: b -> a}

data Lens s' s = Lens { put :: s -> s' -> s', get :: s' -> s}

proj1Lens :: Lens (a, b) a
proj1Lens = Lens {put = \x (_,y) -> (x,y), get = fst}

proj2Lens :: Lens (a, b) b
proj2Lens = Lens {put = \y (x,_) -> (x,y), get = snd}

upgrade :: Lens s' s -> Stream s a -> Stream s' a
upgrade = _

data PackedStream s a where
    L :: forall s' s a.
         s' ->
         Stream (s,s') a ->
         PackedStream s a

switch :: forall a s. StreamTyped a => (s -> EStep s) -> PackedStream s a -> PackedStream s a -> PackedStream s a
switch init (L x0 f) (L y0 f') = go (typeRep @a) init x0 y0 f f'
    where
        go :: forall a s s' s''. TypeRep StreamTyped a -> (s -> EStep s) -> s' -> s'' -> Stream (s,s') a -> Stream (s,s'') a -> PackedStream s a
        go TVoid init x0 y0 (SV v) _ = L () (SV v)
        go TInt init x0 y0 (SI f) (SI f') = L Nothing $ SI $ \(s,m) -> case m of
                                                                         Nothing -> (case init s of
                                                                                      ESkip s' -> Left (s',Nothing)
                                                                                      K1 s' -> Left (s',Just (Left x0))
                                                                                      K2 s' -> Left (s',Just (Right y0))
                                                                                    )
                                                                         Just (Left u) -> _
                                                                         Just (Right v) -> _
        go (TPair a b) init x0 y0 s s' = _
        go (TSum a b) init x0 y0 (S1 f) (S1 f') = _ $ go a init f f'
        go (TSum a b) init x0 y0 (S2 f) (S2 f') = _ $ go b init f f'
        go (TSum a b) init x0 y0 (S1 f) (S2 f') = L _ (SS _ _ _)
        go (TSum a b) init x0 y0 (S2 f) (S1 f') = L _ (SS _ _ _)

        go (TSum a b) init x0 y0 (S1 f) (SS init0 s1 s2) = _
        go (TSum a b) init x0 y0 (S2 f) (SS init0 s1 s2) = _

        go (TSum a b) init x0 y0 (S1 f) (SS init0 s1 s2) = _
        go (TSum a b) init x0 y0 (S2 f) (SS init0 s1 s2) = _

        go (TSum a b) init x0 y0 (SS init0 s1 s2) (SS init0' s1' s2') = _
