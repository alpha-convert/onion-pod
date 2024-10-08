{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TemplateHaskell #-}


module CPSStaged.Stream (
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
    let loop x acc = $$(next [|| x ||] [|| acc ||] (\cx' -> [|| loop $$cx' acc||]) (\ca cx' -> [|| loop $$cx' $$(f [|| acc ||] ca)  ||])) in
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

{-
We can use this businesss to turn the monotonic state changes into actual straight-line control.
-}

sFold' :: (Quote m) => (Code m r -> Code m a -> Code m r) -> Code m (i,r) -> StreamFunc m (i,s') a -> Code m (i,r)
sFold' cf ciacc0 (SF cix0 next) = [||
    let (i0,acc0) = $$ciacc0 in
    let (_,x0) = $$cix0 in
    let loop i x acc = $$(next [|| (i,x) ||]
                               [|| (i,acc) ||] 
                               (\cix' -> [|| let (i',x') = $$cix' in loop i' x' acc ||])
                               (\ca cix' -> [|| let (i',x') = $$cix' in let a = $$ca in let acc' = $$(cf [|| acc ||] [||a||]) in loop i' x' acc' ||])) in 
    loop i0 x0 acc0
 ||]

sFoldS :: (Quote m) => (Code m r -> Code m a -> Code m r) -> Code m (i,r) -> [StreamFunc m (i,s') a] -> Code m (i,r)
sFoldS cf ciz [] = ciz
sFoldS cf ciz (s:ss) = sFoldS cf (sFold' cf ciz s) ss
