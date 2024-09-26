{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}


module StreamCPSStaged (
    Stream(..),
    StreamFunc(..)
) where


import Language.Haskell.TH

data StreamFunc m s a = SF (Code m s) (forall w. Code m s -> Code m w -> (Code m s -> Code m w) -> (Code m a -> Code m s -> Code m w) -> Code m w)

data Stream m a where
    S :: forall m s a. StreamFunc m s a -> Stream m a