{-# LANGUAGE GADTs #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
module StatefulTemplateStream  where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import GHC.STRef (STRef(..), newSTRef, readSTRef, writeSTRef)
import Control.Monad (forM_)
import Control.Monad.ST (ST, runST)
import GHC.Arr
import Control.Applicative

-- Step s a %1 -> w
-- ~=
-- w (*) (s %1 -> w) (*) (a -> s -> w)

data StreamFunc m t s a where
    SF :: forall m t s a. (forall w. 
        (s -> Code m (ST t w)) -> 
            Code m (ST t w)) -> 
                !(forall w. s -> Code m (ST t w) -> 
                    Code m (ST t w) -> 
                        (Code m a -> Code m (ST t w)) -> 
                            Code m (ST t w)) -> StreamFunc m t s a

data Stream m t a where
    S :: forall m t a s. StreamFunc m t s a -> Stream m t a

-- instance Lift (MutVar# s a) where

-- deriving instance Lift (STRef s a)
sFromListFancy :: (Lift a,Quote m) => [a] -> Stream m t a
sFromListFancy xs =
    let n = length xs in
    S $ SF (\k -> [|| do {i <- newSTRef 0; --create index ref
                          arr <- newSTArray (0,n) undefined; -- build new array
                          forM_ (zip [0..] xs) (uncurry (writeSTArray arr));  --fill the array
                          $$(k ([||arr||],[|| i ||]) )}
                  ||]
            )
        (\(c_arr,c_i_ref) done skip yield -> [|| do
            let arr = $$c_arr
            let i_ref = $$c_i_ref
            i <- readSTRef i_ref
            if i == n then $$done else do
                x <- readSTArray arr i
                writeSTRef i_ref (i + 1)
                $$(yield [|| x ||])
            ||])

sFromList :: (Lift a,Quote m) => [a] -> Stream m t a
sFromList xs = S $ SF (\k -> [|| do {ref <- newSTRef xs; $$(k [|| ref ||])} ||]) (\ref done skip yield ->
        [|| do
            ys <- readSTRef $$ref
            case ys of
                [] -> $$done
                z:zs -> writeSTRef $$ref zs >> $$(yield [|| z ||])
        ||]
    )

sFromListCode :: Quote m => Code m [a] -> Stream m t a
sFromListCode c = S $ SF (\k -> [|| do {ref <- newSTRef $$c; $$(k [|| ref ||])} ||]) (\ref done skip yield ->
        [|| do
            ys <- readSTRef $$ref
            case ys of
                [] -> $$done
                z:zs -> writeSTRef $$ref zs >> $$(yield [|| z ||])
        ||]
    )

sFromListCodeFancy :: (Quote m) => Code m [a] -> Stream m t a
sFromListCodeFancy cxs =
    S $ SF (\k -> [|| do {i <- newSTRef 0; --create index ref
                          xs <- return $$cxs;
                          n <- return (length xs);
                          arr <- newSTArray (0,n) undefined; -- build new array
                          forM_ (zip [0..] xs) (uncurry (writeSTArray arr));  --fill the array
                          $$(k ([||arr||],[|| i ||],[|| n ||]) )}
                  ||]
            )
        (\(c_arr,c_i_ref,n) done skip yield -> [|| do
            let arr = $$c_arr
            let i_ref = $$c_i_ref
            i <- readSTRef i_ref
            if i == $$n then $$done else do
                x <- readSTArray arr i
                writeSTRef i_ref (i + 1)
                $$(yield [|| x ||])
            ||])

sFromArrayCode :: Quote m => Code m (STArray t Int a) -> Stream m t a
sFromArrayCode carr =
    S $ SF (\k -> [|| do
                        i <- newSTRef 0; --create index ref
                        let arr = $$carr
                        let (lo,hi) = boundsSTArray arr
                        $$(k ([|| arr ||],[|| i ||],[|| hi - lo ||]) )
                  ||]
            )
        (\(c_arr,c_i_ref,n) done skip yield -> [|| do
            let arr = $$c_arr
            let i_ref = $$c_i_ref
            i <- readSTRef i_ref
            if i == $$n then $$done else do
                x <- readSTArray arr i
                writeSTRef i_ref (i + 1)
                $$(yield [|| x ||])
            ||])

smap :: Quote m => Code m (a -> b) -> Stream m t a -> Stream m t b
smap f (S (SF x0 next)) = S $ SF x0 (\s done skip yield -> next s done skip (\ca -> yield [|| $$f $$ca ||]))

szip :: Quote m => Stream m t a -> Stream m t b -> Stream m t (a,b)
szip (S (SF init next)) (S (SF init' next')) = S $ SF
    (\k -> init (\x -> init' (\x' -> [|| do {ref <- newSTRef Nothing; $$(k (x,x',[|| ref ||]))} ||])))
    (\(x,x',cref) done skip yield ->
        [|| do
            let ref = $$cref
            m <- readSTRef ref
            case m of
                Nothing -> $$(next x done skip (\ca -> [|| writeSTRef ref (Just $$ca) >> $$skip ||]))
                Just a -> $$(next' x' done skip (\cb -> [|| writeSTRef ref Nothing >> $$(yield [|| (a,$$cb) ||]) ||]))
        ||]
    )

sfold :: Quote m => (Code m r -> Code m a -> Code m r) -> Code m r -> Stream m t a -> Code m (ST t r)
sfold f z (S (SF init next)) = init (\x ->
     [|| do
        acc <- newSTRef $$z;
        let loop = $$(next x [|| readSTRef acc ||] [|| loop ||] (\ca -> [|| do { z' <- readSTRef acc; writeSTRef acc $$(f [|| z' ||] ca); loop } ||]))
        loop
    ||]
 )

ssum :: (Quote m) => Stream m t Int -> Code m (ST t Int)
ssum = sfold (\x y -> [|| $$x + $$y ||]) [|| 0 ||]

sCollect :: (Quote m, Alternative f) => Stream m t a -> Code m (ST t (f a))
sCollect = sfold (\cxs cx -> [|| $$cxs <|> pure $$cx ||]) [|| empty ||]

stutter :: (Quote m) => Stream m t a -> Stream m t a
stutter (S (SF init next)) = S $ SF (\k -> init (\s -> [|| do {ref <- newSTRef Nothing; $$(k ([||ref||],s)) } ||])) (\(cref,x) done skip yield ->[||
    do
        let ref = $$cref
        m <- readSTRef ref
        case m of
            Nothing -> $$(next x done skip (\ca -> [|| let a = $$ca in writeSTRef ref (Just a) >> $$(yield [|| a ||]) ||]))
            Just a -> writeSTRef ref Nothing >> $$(yield [|| a ||])
 ||])

test_test :: Quote m => [Int] -> Code m (ST t Int)
test_test xs = ssum (stutter (sFromListFancy xs))

hmm :: Quote m => Code m ([Int] -> ST t Int)
hmm = [|| \xs -> $$(ssum (smap [|| (+1) ||] (stutter (sFromListCode [|| xs ||])))) ||]

dot :: Quote m => Code m ([Int] -> [Int] -> ST t Int)
dot = [|| \xs ys -> $$(ssum (smap [|| (uncurry (*)) ||] (szip (sFromListCode [|| xs ||]) (sFromListCode [|| ys ||])))) ||]

magSquared :: Quote m => Code m ([Int] -> ST t Int)
magSquared = [|| \xs -> $$(ssum (smap [|| \x -> x * x ||] (sFromListCode [|| xs ||]))) ||]

blah :: Quote m => (Code m a -> Code m b) -> Code m (a -> b)
blah f = [|| \x -> $$(f [|| x ||]) ||]