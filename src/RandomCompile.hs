{-# LANGUAGE ViewPatterns, LambdaCase, LinearTypes, TypeFamilies #-}
module Random where

import Data.Map as M
import Data.Maybe

{- 
Consider the following source language.
Top-level terms in the source language have some number of int-type inputs, and return an int. The language
has let-binding for local variables, as well as pairs and arithmetic. The SrcVar constructor can either refer to a let-bound variable,
or to one of the externally-defined inputs.
-}

data SrcTm where
    SrcVar :: String -> SrcTm
    SrcLet :: String -> SrcTm -> SrcTm -> SrcTm
    SrcInt :: Int -> SrcTm
    SrcPair :: SrcTm -> SrcTm -> SrcTm
    SrcProj1 :: SrcTm -> SrcTm 
    SrcProj2 :: SrcTm -> SrcTm 
    SrcAdd :: SrcTm -> SrcTm -> SrcTm

{-
In principle, these programs should just be arithmetic combinations of constants and input variables.
Let's compile to a target language where only those constructs are present.
-}

data TgtTm where
    TgtVar :: String -> TgtTm
    TgtInt :: Int -> TgtTm
    TgtAdd :: TgtTm -> TgtTm -> TgtTm

{-
The trick is to instead compile into the following richer language: top-level tuples of base terms.
We'll call these tuples "Rows".
Think about why this works! It's very much related to fusion!
-}
data Row where
    Base :: TgtTm -> Row
    Pair :: Row -> Row -> Row

compile' :: Map String Row -> SrcTm -> Row
compile' eta (SrcVar x) = fromJust (M.lookup x eta)
compile' eta (SrcLet x e1 e2) = compile' (M.insert x (compile' eta e1) eta) e2
compile' _ (SrcInt v) = Base (TgtInt v)
compile' eta (SrcPair e1 e2) = Pair (compile' eta e1) (compile' eta e2)
compile' eta (SrcProj1 e) = let (Pair tt' _) = compile' eta e in tt'
compile' eta (SrcProj2 e) = let (Pair _ tt') = compile' eta e in tt'
compile' eta (SrcAdd e e') =
    let (Base c) = compile' eta e in
    let (Base c') = compile' eta e' in
    Base (TgtAdd c c')

compile :: [String] -> SrcTm -> TgtTm
compile fvs src =
    let m = M.fromList (Prelude.map (\x -> (x,Base (TgtVar x))) fvs) in
    let (Base tgt) = compile' m src in tgt