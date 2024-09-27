{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TemplateHaskell #-}


module StreamCPSStaged (
    Stream(..),
    StreamFunc(..),
    sFromList',
    sToList
) where


import Language.Haskell.TH
import Language.Haskell.TH.Syntax

{-
data StreamFunc m s a = SF (Code m s) (Code m s -> Code m (Step s a))
-}

data StreamFunc m s a = SF (Code m s) (forall w. Code m s -> Code m w -> (Code m s -> Code m w) -> (Code m a -> Code m s -> Code m w) -> Code m w)

data Stream m a where
    S :: forall m s a. StreamFunc m s a -> Stream m a

sFold :: (Quote m) => (Code m r -> Code m a -> Code m r) -> Code m r -> Stream m a -> Code m r
sFold f z (S (SF x0 next)) = [||
    let loop x acc = $$(next [|| x ||] [|| acc ||] (\cx' -> [|| loop $$cx' acc||]) (\ca cx' -> [|| let acc' = $$(f [|| acc ||] ca) in loop $$cx' acc' ||])) in
    loop $$x0 $$z
 ||]

sToList :: (Quote m) => Stream m a -> Code m [a]
sToList = sFold (\cxs cx -> [|| $$cxs ++ [$$cx] ||]) [|| [] ||]

sFromList :: (Quote m) => Code m [a] -> Stream m a
sFromList cxs = S $ SF cxs $ \cxs' done _ yield -> [||
    case $$cxs' of 
        [] -> $$done
        x:xs -> $$(yield [||x||] [||xs||])
 ||]

sFromList' :: (Quote m, Lift a) => [a] -> Stream m a
sFromList' xs = sFromList [|| xs ||]