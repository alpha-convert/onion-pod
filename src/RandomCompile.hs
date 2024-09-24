{-# LANGUAGE ViewPatterns, LambdaCase, LinearTypes, TypeFamilies, GADTs #-}
module RandomCompile where

import Data.Map as M
import Data.Maybe

data SrcTm where
    SrcVar :: String -> SrcTm
    SrcLet :: String -> SrcTm -> SrcTm -> SrcTm
    SrcInt :: Int -> SrcTm
    SrcPair :: SrcTm -> SrcTm -> SrcTm
    SrcProj1 :: SrcTm -> SrcTm 
    SrcProj2 :: SrcTm -> SrcTm 
    SrcAdd :: SrcTm -> SrcTm -> SrcTm


data TgtTm where
    TgtVar :: String -> TgtTm
    TgtInt :: Int -> TgtTm
    TgtAdd :: TgtTm -> TgtTm -> TgtTm

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