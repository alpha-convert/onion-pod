{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Stream (
    Step(..),
    Stream(..),
    StreamFunc(..),
    genStreamFromList,
    sFromList,
    sToList
) where

import Control.Monad.State.Strict
import Control.Monad
import Test.QuickCheck (Arbitrary, frequency)
import Test.QuickCheck.Gen (Gen)

data Step s a where
    Done :: Step s a
    Skip :: s -> Step s a
    Yield :: a -> s -> Step s a

data StreamFunc s a where
    SF :: forall s a. s -> (s -> Step s a) -> StreamFunc s a

{-
data Step i j s a where
    Done :: Step i j s a
    Skip :: i -> s -> Step i j s a
    Yield :: a -> i -> s -> Step i j s a
    Jump :: i -> j -> Step i j s a

j NEEDS TO BE KNOWN DYNAMICALLY! j is NOT CODE!

data StepFuncs i s a where
    SFs :: forall i s a. forall j -> (s -> Step i j s a) -> (j -> StepFuncs i s a) -> StepFuncs i s a
-}

data Stream a where
    S :: forall a s. StreamFunc s a -> Stream a

ssink :: Stream a
ssink = S (SF () (const Done))

scons :: a -> Stream a -> Stream a
scons a (S (SF x0 next)) = S $ SF Nothing $
    \case
        Nothing -> Yield a (Just x0)
        Just (next -> Done) -> Done
        Just (next -> Skip x) -> Skip (Just x)
        Just (next -> Yield a x) -> Yield a (Just x)

instance Foldable Stream where
    foldr f y0 (S (SF x0 next)) = go (x0,y0)
        where
            go (next -> Done,y) = y
            go (next -> Skip x,y) = go (x,y)
            go (next -> Yield a x,y) = go (x,f a y)

sFromList :: [a] -> Stream a
sFromList = foldr scons ssink

sToList :: Stream a -> [a]
sToList = foldr (\x xs -> xs ++ [x]) []

intersperseNothings [] = return []
intersperseNothings (x:xs) = do
    b <- frequency [(10,return True),(7,return False)]
    if b then (Just x:) <$> intersperseNothings xs
    else (Nothing:) <$> intersperseNothings (x:xs)

genStreamFromList :: [a] -> Gen (Stream a)
genStreamFromList xs = do
    xms <- intersperseNothings xs
    return (S (SF xms next))
        where
            
            next [] = Done
            next (Nothing:xs) = Skip xs
            next (Just a:xs) = Yield a xs

-- ssing :: a -> Stream a
-- ssing x = S $ SF False (\b -> if not b then Yield x True else Done)

-- srepeat :: a -> Stream a
-- srepeat x = S $ SF () $ const $ Yield x ()

-- stail :: Stream a -> Stream a
-- stail (S (SF x0 next)) = S $ SF (x0,False) $
--     \case
--         (next -> Done,_) -> Done
--         (next -> Skip x,b) -> Skip (x,b)
--         (next -> Yield a x,False) -> Skip (x,True)
--         (next -> Yield a x,True) -> Yield a (x,True)

-- smap :: (a -> b) -> Stream a -> Stream b
-- smap f (S (SF x0 next)) = S $ SF x0 $
--     \x -> case next x of
--             Done -> Done
--             Skip x' -> Skip x'
--             Yield a x' -> Yield (f a) x'

-- smapMaybe :: (a -> Maybe b) -> Stream a -> Stream b
-- smapMaybe f (S (SF x0 next)) = S $ SF x0 $
--     \case
--         (next -> Done) -> Done
--         (next -> Skip x) -> Skip x
--         (next -> Yield (f -> Nothing) x) -> Skip x
--         (next -> Yield (f -> Just b) x) -> Yield b x

-- sfilter :: (a -> Bool) -> Stream a -> Stream a
-- sfilter f = smapMaybe (\x -> if f x then Just x else Nothing)

-- sstatefulmap :: s -> (a -> State s (Maybe b)) -> Stream a -> Stream b
-- sstatefulmap y0 f (S (SF x0 next)) = S $ SF (x0,y0) $
--     \case
--         (next -> Done,_) -> Done
--         (next -> Skip x,y) -> Skip (x,y)
--         (next -> Yield a x,y) -> case runState (f a) y of
--                                     (Just b,y') -> Yield b (x,y')
--                                     (Nothing,y') -> Skip (x,y')

-- sapplyFirst :: (a -> a) -> Stream a -> Stream a
-- sapplyFirst f = sstatefulmap False $ \a -> do
--     pastFirst <- get
--     if pastFirst then do
--         return (Just a)
--     else do
--         put True
--         return (Just (f a))

-- sbind :: Stream a -> (a -> Stream b) -> Stream b
-- sbind (S (SF x0 next)) f = S $ SF (x0,Nothing) $
--     \case
--         (x',Just (S (SF x'' next'))) -> case next' x'' of
--                                             Done -> Skip (x', Nothing)
--                                             Skip x''' -> Skip (x', Just (S (SF x''' next')))
--                                             Yield b x''' -> Yield b (x', Just (S (SF x''' next')))
--         (next -> Done,Nothing) -> Done
--         (next -> Skip x,Nothing) -> Skip (x,Nothing)
--         (next -> Yield a x,Nothing) -> Skip (x, Just (f a))


-- statefulSBind :: Stream a -> s -> (s -> a -> (s, Stream b)) -> Stream b
-- statefulSBind (S (SF x0 next)) y0 f = S $ SF (x0,y0,Nothing) $
--     \case
--         (x',y',Just (S (SF x'' next'))) -> case next' x'' of
--                                             Done -> Skip (x',y', Nothing)
--                                             Skip x''' -> Skip (x', y',Just (S (SF x''' next')))
--                                             Yield b x''' -> Yield b (x', y', Just (S (SF x''' next')))
--         (next -> Done,y,Nothing) -> Done
--         (next -> Skip x,y,Nothing) -> Skip (x,y,Nothing)
--         (next -> Yield a x,y,Nothing) -> let (y',bs) = f y a in
--                                          Skip (x,y', Just bs)

-- szip :: Stream a -> Stream b -> Stream (a,b)
-- szip (S (SF x0 next)) (S (SF y0 next')) = S $ SF (x0,y0,Nothing) $
--     \case
--         (next -> Done,y,Nothing) -> Done
--         (next -> Skip x',y,Nothing) -> Skip (x',y,Nothing)
--         (next -> Yield a x',y,Nothing) -> Skip (x',y,Just a)
--         (x,next' -> Done,Just a) -> Done
--         (x,next' -> Skip y',Just a) -> Skip (x,y',Just a)
--         (x,next' -> Yield b y',Just a) -> Yield (a,b) (x,y',Nothing)

-- sconcat :: Stream a -> Stream a -> Stream a
-- sconcat (S (SF x0 next)) (S (SF y0 next')) = S $ SF (Left x0) $
--     \case
--         (Left (next -> Done)) -> Skip (Right y0)
--         (Left (next -> Skip x)) -> Skip (Left x)
--         (Left (next -> Yield a x)) -> Yield a (Left x)
--         (Right (next' -> Done)) -> Done
--         (Right (next' -> Skip y)) -> Skip (Right y)
--         (Right (next' -> Yield a y)) -> Yield a (Right y)

-- {-
-- sconcat ssink s
--   = sconcat (S $ SF () (const Done)) (S (SF y0 next')) 
--   = S $ (SF (Left ())) $
--         \case
--             (Left (const Done -> Done)) -> Skip (Right y0)
--             (Left (const Done -> Skip x)) -> Skip (Left x)
--             (Left (const Done -> Yield a x)) -> Yield a (Left x)
--             (Right (next' -> Done)) -> Done
--             (Right (next' -> Skip y)) -> Skip (Right y)
--             (Right (next' -> Yield a y)) -> Yield a (Right y)
--   =  S $ (SF (Left ())) $
--         \case
--             (Left ()) -> Skip (Right y0)
--             (Right (next' -> Done)) -> Done
--             (Right (next' -> Skip y)) -> Skip (Right y)
--             (Right (next' -> Yield a y)) -> Yield a (Right y)
--   ~= s (bisimulation: equivalent up to skips.)
-- -}

-- yieldStates :: StreamFunc s a -> StreamFunc s s
-- yieldStates (SF x0 next) = SF x0 $
--     \case
--         (next -> Done) -> Done
--         (next -> Skip x) -> Yield x x
--         (next -> Yield _ x) -> Yield x x

-- stakeWhile :: (a -> Bool) -> Stream a -> Stream a
-- stakeWhile p (S (SF x0 next)) = S $ SF x0 next'
--     where
--         next' (next -> Done) = Done
--         next' (next -> Skip x) = Skip x
--         next' (next -> Yield a x) = if p a then Yield a x else Done


-- stakeWhileSt :: s -> (a -> State s Bool) -> Stream a -> Stream a
-- stakeWhileSt x0 f (S (SF y0 next)) = S (SF (y0,x0) next')
--     where
--         next' (next -> Done,_) = Done
--         next' (next -> Skip y,x) = Skip (y,x)
--         next' (next -> Yield a y,x) = let (b,x') = runState (f a) x in if b then Yield a (y,x') else Done

-- sdropWhile :: (a -> Bool) -> Stream a -> Stream a
-- sdropWhile p (S (SF x0 next)) = S $ SF (x0,True) next'
--     where
--         next' (next -> Done,_) = Done
--         next' (next -> Skip x,b) = Skip (x,b)
--         next' (next -> Yield a x,False) = Yield a (x,True)
--         next' (next -> Yield a x,True) = if p a then Skip (x,True) else Yield a (x,False)

-- sdropWhileSt :: s -> (a -> State s Bool) -> Stream a -> Stream a
-- sdropWhileSt x0 f (S (SF y0 next)) = S (SF (y0,x0,True) next')
--     where
--         next' (next -> Done,_,_) = Done
--         next' (next -> Skip y,x,b) = Skip (y,x,b)
--         next' (next -> Yield a y,x,False) = Yield a (y,x,False)
--         next' (next -> Yield a y,x,True) = let (b,x') = runState (f a) x in if b then Skip (y,x',True) else Yield a (y,x',False)


-- sspan :: (a -> Bool) -> Stream a -> (Stream a, Stream a)
-- sspan p s = (stakeWhile p s, sdropWhile p s)

-- -- (sappend (stakewhile p s) (sdropwhile p s)) == s

-- spartition :: (a -> Either b c) -> Stream a -> (Stream b, Stream c)
-- spartition f (S (SF x0 next)) = (S (SF x0 next1), S (SF x0 next2))
--     where
--         next1 (next -> Done) = Done
--         next1 (next -> Skip x) = Skip x
--         next1 (next -> Yield (f -> Left b) x) = Yield b x
--         next1 (next -> Yield (f -> _) x) = Skip x

--         next2 (next -> Done) = Done
--         next2 (next -> Skip x) = Skip x
--         next2 (next -> Yield (f -> Right c) x) = Yield c x
--         next2 (next -> Yield (f -> _) x) = Skip x
-- {-
-- alternatively, spartition f s = smux (srepeat f) s
-- -}

-- instance Show a => Show (Stream a) where
--     show = show . sToList

-- sMux :: Stream (a -> Either b c) -> Stream a -> (Stream b,Stream c)
-- sMux fs as =
--     let ebcs = (\(f,a) -> f a) <$> szip fs as in
--     (ebcs >>= either return (const mempty),ebcs >>= either (const mempty) return)

-- sRepeatFirst :: Stream a -> Stream a
-- sRepeatFirst (S (SF x0 next)) = S $ SF (x0,Nothing) $
--     \case
--         (next -> Done,Nothing) -> Done
--         (next -> Skip x,Nothing) -> Skip (x,Nothing)
--         (next -> Yield a x,Nothing) -> Yield a (x,Just a)
--         s@(x,Just a) -> Yield a s



-- {- applies the condition to the first element of the input stream, and then switches to one or the other -}
-- sIf :: (a -> Bool) -> Stream a -> Stream b -> Stream b -> Stream b
-- sIf p (S (SF x0 next)) (S (SF y0 next0)) (S (SF y1 next1)) = S (SF (Left x0) next')
--     where
--         next' (Left (next -> Done)) = Done
--         next' (Left (next -> Skip x)) = Skip (Left x)
--         next' (Left (next -> Yield a _)) = if p a then Skip (Right (Left y0)) else Skip (Right (Right y1))
--         next' (Right (Left (next0 -> Done))) = Done
--         next' (Right (Left (next0 -> Skip y))) = Skip (Right (Left y))
--         next' (Right (Left (next0 -> Yield b y))) = Yield b (Right (Left y))
--         next' (Right (Right (next1-> Done))) = Done
--         next' (Right (Right (next1 -> Skip y))) = Skip (Right (Right y))
--         next' (Right (Right (next1 -> Yield b y))) = Yield b (Right (Right y))


-- instance Monad Stream where
--     return = pure
--     (>>=) = sbind

-- instance Applicative Stream where
--     pure = ssing
--     liftA2 = liftM2

-- instance Semigroup (Stream a) where
--     (<>) = sconcat

-- instance Monoid (Stream a) where
--     mempty = ssink

-- {- unclear if this instance behaves well with regards to fusion... probably depends on f? -}
-- instance Traversable Stream where
--     traverse f (S (SF x0 next)) = go x0
--         where
--             go (next -> Done) = pure ssink
--             go (next -> Skip x) = go x
--             go (next -> Yield a x) = scons <$> f a <*> go x

-- instance Functor Stream where
--     fmap f (S (SF x next)) = S $ SF x $
--         \case
--             (next -> Done) -> Done
--             (next -> Skip x) -> Skip x
--             (next -> Yield a x) -> Yield (f a) x
