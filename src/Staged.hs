{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TemplateHaskell #-}

module Staged where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

data Term = Id | Compose Term Term | Map (Int -> Int) | Filter (Int -> Bool) | Scan (Int -> Int -> Int)

denote :: Term -> ([Int] -> [Int])