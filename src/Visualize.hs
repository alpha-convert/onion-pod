{-# LANGUAGE TemplateHaskell #-}

module Visualize where

import Test.QuickCheck
import qualified Test.Tyche as Tyche
import Term

-- Desired properties:
-- Depth of term
-- Proportion of variables in the context used in the term
-- Do variables in the extended context get used?
-- Outermost expression, e.g., Var, CatR, etc
-- Diversity of expressions
