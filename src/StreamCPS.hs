{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module StreamCPS (
    Stream(..),
    StreamFunc(..),
    sFromList,
    sToList,
) where

data StreamFunc s a = SF {
  state :: s, 
  next :: forall w. s -> w -> (s -> w) -> (a -> s -> w) -> w
  }

data Stream a where
    S :: forall s a. StreamFunc s a -> Stream a

sFromList :: [a] -> Stream a
sFromList xs = S ( SF { state = xs, next = next' } )
  where
    next' [] done _ _ = done                 
    next' (y:ys) _ _ yield = yield y ys

instance Foldable Stream where
  foldr f y0 (S SF { .. }) = go state
    where
      go st = next st y0 go (\a s' -> f a (go s'))

sToList :: Stream a -> [a]
sToList = foldr (:) []

smapCps :: (a -> b) -> Stream a -> Stream b
smapCps (f :: a -> b) (S (SF @s x0 next')) = S (SF @s x0 next'')
  where
    next'' :: forall w. s -> w -> (s -> w) -> (b -> s -> w) -> w
    next'' st done skip yield = next' st done skip (\a s' -> yield (f a) s')

smapMaybeCps :: (a -> Maybe b) -> Stream a -> Stream b
smapMaybeCps (f :: a -> Maybe b) (S (SF @s x0 next')) = S (SF @s x0 next'')
  where
    next'' :: forall w. s -> w -> (s -> w) -> (b -> s -> w) -> w
    next'' st done skip yield = next' st done skip (\a s' ->
      case f a of
        Nothing -> skip s'
        Just b -> yield b s'
      )

sfilter :: (a -> Bool) -> Stream a -> Stream a
sfilter f = smapMaybeCps (\x -> if f x then Just x else Nothing)