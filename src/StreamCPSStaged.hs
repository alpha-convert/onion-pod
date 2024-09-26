{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module StreamCPSStaged (
    StreamCPS(..),
    StreamFuncCps(..),
    sFromList,
    sToList,
) where

data StreamFuncCps s a = SFCps {
  state :: s, 
  next :: forall w. s -> w -> (s -> w) -> (a -> s -> w) -> w
  }

data StreamCPS a where
    S :: forall s a. StreamFuncCps s a -> StreamCPS a

sFromList :: [a] -> StreamCPS a
sFromList xs = S ( SFCps { state = xs, next = next' } )
  where
    next' [] done _ _ = done                 
    next' (y:ys) _ _ yield = yield y ys

instance Foldable StreamCPS where
  foldr f y0 (S SFCps { .. }) = go state
    where
      go st = next st y0 go (\a s' -> f a (go s'))

sToList :: StreamCPS a -> [a]
sToList = foldr (:) []

smapCps :: (a -> b) -> StreamCPS a -> StreamCPS b
smapCps (f :: a -> b) (S (SFCps @s x0 next')) = S (SFCps @s x0 next'')
  where
    next'' :: forall w. s -> w -> (s -> w) -> (b -> s -> w) -> w
    next'' st done skip yield = next' st done skip (\a s' -> yield (f a) s')

smapMaybeCps :: (a -> Maybe b) -> StreamCPS a -> StreamCPS b
smapMaybeCps (f :: a -> Maybe b) (S (SFCps @s x0 next')) = S (SFCps @s x0 next'')
  where
    next'' :: forall w. s -> w -> (s -> w) -> (b -> s -> w) -> w
    next'' st done skip yield = next' st done skip (\a s' ->
      case f a of
        Nothing -> skip s'
        Just b -> yield b s'
      )

sfilter :: (a -> Bool) -> StreamCPS a -> StreamCPS a
sfilter f = smapMaybeCps (\x -> if f x then Just x else Nothing)