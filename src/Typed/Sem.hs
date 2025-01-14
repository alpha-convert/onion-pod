{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Typed.Sem where

import Typed.NormalForm
import Events
import Typed.Stream
import Control.Monad.ST (runST)
import Control.Monad.State (execState, evalState)
import Data.Void
import Data.Functor.Const
import Data.Function ((&))
import Typed.Hoas (StreamTyped)

sem :: StreamTyped a => forall s. Nf (Stream s) a -> PackedStream s a
sem (NUp (NBoundVar s)) = L () (upgrade proj1Lens s)
sem (NLift b) = _
sem NEpsR = L () SV
sem (NCatR @a @b e e') =
    sem e & \(L x0 f) ->
    sem e' & \(L y0 f') ->
    L (x0,y0) (SP (upgrade _ f) (upgrade _ f'))
sem (NCatL (NBoundVar (SP s1 s2)) k) = sem (k s1 s2)
sem (NPlusCase (NBoundVar (SS init s s')) cont1 cont2) = switch init (sem (cont1 s)) (sem (cont2 s'))
sem (NPlusCase (NBoundVar (S1 s)) cont1 _) = sem (cont1 s)
sem (NPlusCase (NBoundVar (S2 s)) _ cont2) = sem (cont2 s)

sem (NInl e) =
    sem e & \(L x0 f) -> L x0 (S1 f)
sem (NInr e) =
    sem e & \(L x0 f) -> L x0 (S2 f)