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
module Imperative.Stream where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import GHC.STRef (STRef(..), newSTRef, readSTRef, writeSTRef)
import Control.Monad.ST (ST, runST)


data StreamFunc m t i a where
    SF :: forall m t i s a.
            (forall w. (s -> Code m (ST t w)) -> Code m (ST t w)) -> 
            (forall w. i -> s -> Code m (ST t w) -> Code m (ST t w) -> (Code m a -> Code m (ST t w)) -> Code m (ST t w)) ->
            StreamFunc m t i a

data Stream m t i a where
    S :: forall m t i a. (forall w. (i -> Code m (ST t w)) -> Code m (ST t w)) -> StreamFunc m t i a -> Stream m t i a


data IStream m t i a where
    IS :: forall m t i a.
          (forall w. (i -> Code m (ST t w)) -> Code m (ST t w)) ->
          (forall w. i -> Code m (ST t w) -> Code m (ST t w) -> (Code m a -> Code m (ST t w)) -> Code m (ST t w)) ->
          IStream m t i a

sfold :: Quote m => (Code m r -> Code m a -> Code m r) -> Code m r -> Stream m t i a -> Code m (ST t r)
sfold f z (S iinit (SF sinit next)) = iinit $ \i -> sinit $ \x ->
    [|| do
            acc_ref <- newSTRef $$z
            let loop = $$(next i x [|| readSTRef acc_ref ||] [||loop||]
                           (\cev -> [|| do
                                acc <- readSTRef acc_ref
                                writeSTRef acc_ref $$(f [|| acc ||] cev)
                                loop
                            ||])
                         )
            loop
    ||]

-- sFromListFancy :: (Lift a,Quote m) => [a] -> Stream m t a
-- sFromListFancy xs =
--     let n = length xs in
--     S $ SF (\k -> [|| do {i <- newSTRef 0; --create index ref
--                           arr <- newSTArray (0,n) undefined; -- build new array
--                           forM_ (zip [0..] xs) (uncurry (writeSTArray arr));  --fill the array
--                           $$(k ([||arr||],[|| i ||]) )}
--                   ||]
--             )
--         (\(c_arr,c_i_ref) done skip yield -> [|| do
--             let arr = $$c_arr
--             let i_ref = $$c_i_ref
--             i <- readSTRef i_ref
--             if i == n then $$done else do
--                 x <- readSTArray arr i
--                 writeSTRef i_ref (i + 1)
--                 $$(yield [|| x ||])
--             ||])

sFromList :: (Lift a, Quote m) => [a] -> IStream m t (Code m (STRef t [a])) a
sFromList xs = IS (\k -> [|| do {inp_ref <- newSTRef xs; $$(k [|| inp_ref ||])} ||])
               (\inp_ref done _ yield -> [|| do
                    inp_list <- readSTRef $$inp_ref
                    case inp_list of
                        [] -> $$done
                        y:ys -> writeSTRef $$inp_ref ys >> $$(yield [|| y ||])
               ||])

-- sFromList :: (Lift a,Quote m) => [a] -> Stream m t a
-- sFromList xs = S $ SF (\k -> [|| do {ref <- newSTRef xs; $$(k [|| ref ||])} ||]) (\ref done skip yield ->
--         [|| do
--             ys <- readSTRef $$ref
--             case ys of
--                 [] -> $$done
--                 z:zs -> writeSTRef $$ref zs >> $$(yield [|| z ||])
--         ||]
--     )

-- sFromListCode :: Quote m => Code m [a] -> Stream m t a
-- sFromListCode c = S $ SF (\k -> [|| do {ref <- newSTRef $$c; $$(k [|| ref ||])} ||]) (\ref done skip yield ->
--         [|| do
--             ys <- readSTRef $$ref
--             case ys of
--                 [] -> $$done
--                 z:zs -> writeSTRef $$ref zs >> $$(yield [|| z ||])
--         ||]
--     )

-- sFromListCodeFancy :: (Quote m) => Code m [a] -> Stream m t a
-- sFromListCodeFancy cxs =
--     S $ SF (\k -> [|| do {i <- newSTRef 0; --create index ref
--                           xs <- return $$cxs;
--                           n <- return (length xs);
--                           arr <- newSTArray (0,n) undefined; -- build new array
--                           forM_ (zip [0..] xs) (uncurry (writeSTArray arr));  --fill the array
--                           $$(k ([||arr||],[|| i ||],[|| n ||]) )}
--                   ||]
--             )
--         (\(c_arr,c_i_ref,n) done skip yield -> [|| do
--             let arr = $$c_arr
--             let i_ref = $$c_i_ref
--             i <- readSTRef i_ref
--             if i == $$n then $$done else do
--                 x <- readSTArray arr i
--                 writeSTRef i_ref (i + 1)
--                 $$(yield [|| x ||])
--             ||])

-- sFromArrayCode :: Quote m => Code m (STArray t Int a) -> Stream m t a
-- sFromArrayCode carr =
--     S $ SF (\k -> [|| do
--                         i <- newSTRef 0; --create index ref
--                         let arr = $$carr
--                         let (lo,hi) = boundsSTArray arr
--                         $$(k ([|| arr ||],[|| i ||],[|| hi - lo ||]) )
--                   ||]
--             )
--         (\(c_arr,c_i_ref,n) done skip yield -> [|| do
--             let arr = $$c_arr
--             let i_ref = $$c_i_ref
--             i <- readSTRef i_ref
--             if i == $$n then $$done else do
--                 x <- readSTArray arr i
--                 writeSTRef i_ref (i + 1)
--                 $$(yield [|| x ||])
--             ||])

-- smap :: Quote m => Code m (a -> b) -> Stream m t a -> Stream m t b
-- smap f (S (SF x0 next)) = S $ SF x0 (\s done skip yield -> next s done skip (\ca -> yield [|| $$f $$ca ||]))

-- szip :: Quote m => Stream m t a -> Stream m t b -> Stream m t (a,b)
-- szip (S (SF init next)) (S (SF init' next')) = S $ SF
--     (\k -> init (\x -> init' (\x' -> [|| do {ref <- newSTRef Nothing; $$(k (x,x',[|| ref ||]))} ||])))
--     (\(x,x',cref) done skip yield ->
--         [|| do
--             let ref = $$cref
--             m <- readSTRef ref
--             case m of
--                 Nothing -> $$(next x done skip (\ca -> [|| writeSTRef ref (Just $$ca) >> $$skip ||]))
--                 Just a -> $$(next' x' done skip (\cb -> [|| writeSTRef ref Nothing >> $$(yield [|| (a,$$cb) ||]) ||]))
--         ||]
--     )



ssum :: (Quote m) => Stream m t i Int -> Code m (ST t Int)
ssum = sfold (\x y -> [|| $$x + $$y ||]) [|| 0 ||]

sToList :: (Quote m) => Stream m t i a -> Code m (ST t [a])
sToList = sfold (\x y -> [|| $$x ++ [$$y] ||]) [|| [] ||]

-- sCollect :: (Quote m, Alternative f) => Stream m t a -> Code m (ST t (f a))
-- sCollect = sfold (\cxs cx -> [|| $$cxs <|> pure $$cx ||]) [|| empty ||]

-- stutter :: (Quote m) => Stream m t a -> Stream m t a
-- stutter (S (SF init next)) = S $ SF (\k -> init (\s -> [|| do {ref <- newSTRef Nothing; $$(k ([||ref||],s)) } ||])) (\(cref,x) done skip yield ->[||
--     do
--         let ref = $$cref
--         m <- readSTRef ref
--         case m of
--             Nothing -> $$(next x done skip (\ca -> [|| let a = $$ca in writeSTRef ref (Just a) >> $$(yield [|| a ||]) ||]))
--             Just a -> writeSTRef ref Nothing >> $$(yield [|| a ||])
--  ||])

-- test_test :: Quote m => [Int] -> Code m (ST t Int)
-- test_test xs = ssum (stutter (sFromListFancy xs))

-- hmm :: Quote m => Code m ([Int] -> ST t Int)
-- hmm = [|| \xs -> $$(ssum (smap [|| (+1) ||] (stutter (sFromListCode [|| xs ||])))) ||]

-- dot :: Quote m => Code m ([Int] -> [Int] -> ST t Int)
-- dot = [|| \xs ys -> $$(ssum (smap [|| (uncurry (*)) ||] (szip (sFromListCode [|| xs ||]) (sFromListCode [|| ys ||])))) ||]

-- magSquared :: Quote m => Code m ([Int] -> ST t Int)
-- magSquared = [|| \xs -> $$(ssum (smap [|| \x -> x * x ||] (sFromListCode [|| xs ||]))) ||]

-- blah :: Quote m => (Code m a -> Code m b) -> Code m (a -> b)
-- blah f = [|| \x -> $$(f [|| x ||]) ||]