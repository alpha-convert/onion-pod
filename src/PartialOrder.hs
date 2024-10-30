{-# LANGUAGE FlexibleInstances #-}

module PartialOrder (
    Pair,
    Pairs,   
    empty,      
    singleton,     
    contains,    
    insert,         
    delete,        
    lessThan,    
    greaterThan,    
    comparable,     
    toList,                  
    transitiveClosure, 
    union,           
    (|>),          
    concat',       
    allInOrder,     
    subst,         
    substAll,     
    antisymmetric    
) where

import qualified Data.Set as Set

newtype Pair = Pair (String, String) deriving (Eq, Show)

instance Ord Pair where
  compare (Pair (a1, a2)) (Pair (b1, b2)) =
    let first = compare a1 b1
    in if first == EQ then compare a2 b2 else first

type Pairs = Set.Set Pair

empty :: Pairs
empty = Set.empty

singleton :: (String, String) -> Pairs
singleton = Set.singleton . Pair

contains :: (String, String) -> Pairs -> Bool
contains p = Set.member (Pair p)

insert :: (String, String) -> Pairs -> Pairs
insert p = Set.insert (Pair p)

delete :: String -> Pairs -> Pairs
delete a s = Set.foldr (\(Pair (b, c)) acc -> 
    if b == a || c == a 
    then acc
    else Set.insert (Pair (b, c)) acc) Set.empty s

lessThan :: String -> String -> Pairs -> Bool
lessThan a b s = Set.member (Pair (a, b)) s

greaterThan :: String -> String -> Pairs -> Bool
greaterThan a b s = Set.member (Pair (a, b)) s

comparable :: String -> String -> Pairs -> Bool
comparable a b s = lessThan a b s || lessThan b a s

toList :: Pairs -> [(String, String)]
toList = map (\(Pair p) -> p) . Set.toList

transitiveClosure :: Pairs -> Pairs
transitiveClosure s = 
  let trans (Pair (a, b)) (Pair (c, d)) = if b == c then Set.singleton (Pair (a, d)) else Set.empty
      step s' = Set.foldr (\elt acc -> Set.union acc (Set.foldr (Set.union . trans elt) Set.empty s')) Set.empty s'
      nextStep = step s
  in if Set.size nextStep == Set.size s then s else transitiveClosure nextStep

union :: Pairs -> Pairs -> Pairs
union s1 s2 = transitiveClosure (Set.union s1 s2)

(|>) :: a -> (a -> b) -> b
x |> f = f x

concat' :: Pairs -> Pairs -> Pairs
concat' s1 s2 = 
  let s12 = union s1 s2
      newPairs = Set.fromList [Pair (a, b) | Pair (a, _) <- Set.toList s1, Pair (_, b) <- Set.toList s2]
  in transitiveClosure (Set.union s12 newPairs)

allInOrder :: [String] -> Pairs
allInOrder [] = Set.empty
allInOrder (h:t) = concat' (singleton (h, h)) (allInOrder t)

subst :: String -> String -> Pairs -> Pairs
subst x y s = Set.foldr (\(Pair (a, b)) acc -> 
    let a' = if a == y then x else a
        b' = if b == y then x else b
    in Set.insert (Pair (a', b')) acc) Set.empty s
    |> transitiveClosure

substAll :: [String] -> String -> Pairs -> Pairs
substAll xs y s = Set.foldr (\(Pair (a, b)) acc ->
    foldl (\acc' x -> 
        let a' = if a == y then x else a
            b' = if b == y then x else b
        in Set.insert (Pair (a', b')) acc') acc xs) Set.empty s
    |> transitiveClosure

antisymmetric :: Pairs -> Maybe (String, String)
antisymmetric s = Set.foldr (\(Pair (a, b)) acc -> 
    case acc of
      Nothing -> if a /= b && lessThan b a s then Just (a, b) else Nothing
      result -> result) Nothing s
