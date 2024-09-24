module CompilerEquivSpec where

import Types ( Ty(..) )
import Term
import Test.QuickCheck (Property, forAll, (===))
import ElimTerm
import Autom (buildAutom, denoteAutom, denoteAutom')
import Events
import Stream
import Data.Foldable (toList)

import Test.Hspec.QuickCheck (prop)
import Test.Hspec
import Test.QuickCheck.Property

main :: IO ()
main = putStrLn "Test suite not yet implemented"

prop_compilesCorrect :: Term -> [(String,Ty)] -> Property
prop_compilesCorrect ev g =
    let eltm = inlineElims ev in
    let (n,aut) = buildAutom eltm in
    forAll (genTaggedEventsForContext g) (\tevs ->
        forAll (genStreamFromList tevs) (\s ->
            toList (denoteAutom' n aut s) === toList (denoteElimTerm' eltm s)
        )
    )

prop_compilesCorrectExact :: ([TaggedEvent] -> [Event]) -> Term -> [(String,Ty)] -> Property
prop_compilesCorrectExact f ev g =
    let eltm = inlineElims ev in
    let (n,aut) = buildAutom eltm in
    forAll (genTaggedEventsForContext g) (\tevs ->
        forAll (genStreamFromList tevs) (\s ->
            (toList (denoteAutom' n aut s) === toList (denoteElimTerm' eltm s))
            .&&.
            (toList (denoteAutom' n aut s) === f tevs)
        )
    )

ccspec :: String -> Term -> [(String,Ty)] -> SpecWith ()
ccspec s e g =  it s $
            property (prop_compilesCorrect e g)

spec :: Spec
spec = do
    describe "Compiler Correctness" $ do
        ccspec "Variable Int" (Var "x" TyInt) [("x",TyInt)]
        ccspec "Variable Int . Int" (Var "x" (TyCat TyInt TyInt)) [("x",TyCat TyInt TyInt)]
        ccspec "Variable Int Weaken 1" (Var "x" (TyCat TyInt TyInt)) [("y", TyStar TyInt),("x",TyCat TyInt TyInt)]
        ccspec "Variable Int Weaken 2" (Var "x" (TyCat TyInt TyInt)) [("y", TyStar TyInt),("x",TyCat TyInt TyInt),("z", TyInt)]

        ccspec "CatR 1" (CatR (IntR 3) (IntR 4)) []
        ccspec "CatR 2" (CatR (IntR 3) (Var "x" TyInt)) [("x",TyInt)]
        ccspec "CatR 3" (CatR (Var "x" TyInt) (IntR 4)) [("x",TyInt)]
        ccspec "CatR 4" (CatR (IntR 3) (Var "x" TyInt)) [("x",TyInt),("y", TyStar TyInt)]
        ccspec "CatR 5" (CatR (Var "x" TyInt) (IntR 4)) [("y", TyStar TyInt),("x",TyInt)]
        ccspec "CatR 6" (CatR (IntR 3) (Var "x" TyInt)) [("x",TyInt),("y", TyStar TyInt),("z", TyCat TyInt TyInt)]
        ccspec "CatR 7" (CatR (Var "x" TyInt) (IntR 4)) [("y", TyStar TyInt),("x",TyInt),("z", TyCat TyInt TyInt)]
        ccspec "CatR 8" (CatR (IntR 3) (Var "x" (TyStar TyInt))) [("x",TyStar TyInt),("y", TyStar TyInt),("z", TyCat TyInt TyInt)]
        ccspec "CatR 9" (CatR (Var "x" (TyStar TyInt)) (IntR 4)) [("y", TyStar TyInt),("x",TyStar TyInt),("z", TyCat TyInt TyInt)]

        ccspec "pi1(z)" (CatL "x" "y" "z" (Var "x" TyInt)) [("z", TyCat TyInt TyInt)]
        ccspec "pi2(z)" (CatL "x" "y" "z" (Var "y" TyInt)) [("z", TyCat TyInt TyInt)]
        ccspec "pi1(z) of star type" (CatL "x" "y" "z" (Var "x" (TyStar TyInt))) [("z", TyCat (TyStar TyInt) (TyStar TyInt))]
        ccspec "pi2(z) of star type" (CatL "x" "y" "z" (Var "y" (TyStar TyInt))) [("z", TyCat (TyStar TyInt) (TyStar TyInt))]

        ccspec "pi1(pi1(z))"  (CatL "x1" "y1" "z" (CatL "x2" "y2" "x1" (Var "x2" TyInt))) [("z", TyCat (TyCat TyInt TyInt) (TyCat TyInt TyInt))]
        ccspec "pi2(pi1(z))"  (CatL "x1" "y1" "z" (CatL "x2" "y2" "x1" (Var "y2" TyInt))) [("z", TyCat (TyCat TyInt TyInt) (TyCat TyInt TyInt))]
        ccspec "pi1(pi2(z))"  (CatL "x1" "y1" "z" (CatL "x2" "y2" "y1" (Var "x2" TyInt))) [("z", TyCat (TyCat TyInt TyInt) (TyCat TyInt TyInt))]
        ccspec "pi2(pi2(z))"  (CatL "x1" "y1" "z" (CatL "x2" "y2" "y1" (Var "y2" TyInt))) [("z", TyCat (TyCat TyInt TyInt) (TyCat TyInt TyInt))]

        ccspec "pi1(pi1(pi1(z)))"  (CatL "x1" "y1" "z" (CatL "x2" "y2" "x1" (CatL "x3" "y3" "x2" (Var "x3" TyInt)))) [("z", TyCat (TyCat (TyCat TyInt TyInt) (TyCat TyInt TyInt)) (TyCat (TyCat TyInt TyInt) (TyCat TyInt TyInt)))]
        ccspec "pi2(pi1(pi1(z)))"  (CatL "x1" "y1" "z" (CatL "x2" "y2" "x1" (CatL "x3" "y3" "x2" (Var "y3" TyInt)))) [("z", TyCat (TyCat (TyCat TyInt TyInt) (TyCat TyInt TyInt)) (TyCat (TyCat TyInt TyInt) (TyCat TyInt TyInt)))]
        ccspec "pi1(pi2(pi1(z)))"  (CatL "x1" "y1" "z" (CatL "x2" "y2" "x1" (CatL "x3" "y3" "y2" (Var "x3" TyInt)))) [("z", TyCat (TyCat (TyCat TyInt TyInt) (TyCat TyInt TyInt)) (TyCat (TyCat TyInt TyInt) (TyCat TyInt TyInt)))]
        ccspec "pi2(pi2(pi1(z)))"  (CatL "x1" "y1" "z" (CatL "x2" "y2" "x1" (CatL "x3" "y3" "y2" (Var "y3" TyInt)))) [("z", TyCat (TyCat (TyCat TyInt TyInt) (TyCat TyInt TyInt)) (TyCat (TyCat TyInt TyInt) (TyCat TyInt TyInt)))]
        ccspec "pi1(pi1(pi2(z)))"  (CatL "x1" "y1" "z" (CatL "x2" "y2" "y1" (CatL "x3" "y3" "x2" (Var "x3" TyInt)))) [("z", TyCat (TyCat (TyCat TyInt TyInt) (TyCat TyInt TyInt)) (TyCat (TyCat TyInt TyInt) (TyCat TyInt TyInt)))]
        ccspec "pi2(pi1(pi2(z)))"  (CatL "x1" "y1" "z" (CatL "x2" "y2" "y1" (CatL "x3" "y3" "x2" (Var "y3" TyInt)))) [("z", TyCat (TyCat (TyCat TyInt TyInt) (TyCat TyInt TyInt)) (TyCat (TyCat TyInt TyInt) (TyCat TyInt TyInt)))]
        ccspec "pi1(pi2(pi2(z)))"  (CatL "x1" "y1" "z" (CatL "x2" "y2" "y1" (CatL "x3" "y3" "y2" (Var "x3" TyInt)))) [("z", TyCat (TyCat (TyCat TyInt TyInt) (TyCat TyInt TyInt)) (TyCat (TyCat TyInt TyInt) (TyCat TyInt TyInt)))]
        ccspec "pi2(pi2(pi2(z)))"  (CatL "x1" "y1" "z" (CatL "x2" "y2" "y1" (CatL "x3" "y3" "y2" (Var "y3" TyInt)))) [("z", TyCat (TyCat (TyCat TyInt TyInt) (TyCat TyInt TyInt)) (TyCat (TyCat TyInt TyInt) (TyCat TyInt TyInt)))]

        ccspec "inl-epsr" (InL EpsR) []
        ccspec "inr-epsr" (InR EpsR) []
        ccspec "inr-int" (InR (IntR 3)) []
        ccspec "inl-int" (InL (IntR 3)) []
        ccspec "inl-var" (InL (Var "x" TyInt)) [("x",TyInt)]
        ccspec "inl-inl-var" (InL (InL (Var "x" TyInt))) [("x",TyInt)]

        ccspec "nil" Nil []
        ccspec "cons-eps" (Cons EpsR Nil) []
        ccspec "cons-const" (Cons (IntR 3) Nil) []
        ccspec "cons-const2" (Cons (IntR 1) (Cons (IntR 2) Nil)) []
        ccspec "cons-const3" (Cons (IntR 1) (Cons (IntR 2) (Cons (IntR 3) Nil))) []
        ccspec "cons-nested-list" (Cons (Cons (IntR 1) Nil) (Cons (IntR 2) (Cons (IntR 3) Nil))) []

        ccspec "cons-var-head" (Cons (Var "x" TyInt) (Cons (IntR 1) (Cons (IntR 2) (Cons (IntR 3) Nil)))) [("x",TyInt)]
        ccspec "cons-var-head-star" (Cons (Var "x" (TyStar TyInt)) (Cons (IntR 1) (Cons (IntR 2) (Cons (IntR 3) Nil)))) [("x",TyStar TyInt)]
        ccspec "cons-var-head-pi1" (CatL "x" "y" "z" $ Cons (Var "x" TyInt) (Cons (IntR 1) (Cons (IntR 2) (Cons (IntR 3) Nil)))) [("z",TyCat TyInt TyInt)]
        ccspec "cons-var-head-pi2" (CatL "x" "y" "z" $ Cons (Var "y" TyInt) (Cons (IntR 1) (Cons (IntR 2) (Cons (IntR 3) Nil)))) [("z",TyCat TyInt TyInt)]
        ccspec "cons-var-tail" (Cons (IntR 3) (Var "xs" (TyStar TyInt))) [("xs",TyStar TyInt)]
        ccspec "cons-var-tail-star" (Cons (IntR 3) (Var "xs" (TyStar TyInt))) [("xs",TyStar TyInt)]

        ccspec "pluscase-const-both" (PlusCase "x" "_" (IntR 0) "_" (IntR 1)) [("x",TyPlus TyEps TyEps)]
        ccspec "pluscase-var-both" (PlusCase "x" "x1" (Var "x1" TyInt) "x2" (Var "x2" TyInt)) [("x",TyPlus TyInt TyInt)]
        ccspec "pluscase-var-both-star" (PlusCase "x" "x1" (Var "x1" (TyStar TyInt)) "x2" (Var "x2" TyInt)) [("x",TyPlus (TyStar TyInt) TyInt)]

        ccspec "pluscase-pi1" (CatL "x" "y" "z" $ PlusCase "x" "y0" (Var "y0" TyInt) "y1" (Var "y1" TyInt)) [("z", TyCat (TyPlus TyInt TyInt) (TyStar TyInt))]
        ccspec "pluscase-pi2" (CatL "x" "y" "z" $ PlusCase "y" "y0" (Var "y0" TyInt) "y1" (Var "y1" TyInt)) [("z", TyCat (TyStar TyInt) (TyPlus TyInt TyInt))]
