module PullFunctionalitySpec where

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

{-
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
-}

exactSemSpec :: String -> Term -> [TaggedEvent] -> [Event] -> SpecWith ()
exactSemSpec s tm inp outp = it s (
    let eltm = inlineElims tm in
    shouldBe (sToList (denoteElimTerm' eltm (sFromList inp))) outp
 )

spec :: Spec
spec = do
    describe "Pull Semantics" $ do
        exactSemSpec "let Noop" (Let "x" (IntR 3) (Var "x" TyInt)) [] [IntEv 3]
        exactSemSpec "let no jumpiness" (Let "x" (IntR 3) (CatR (Var "y" TyInt) (Var "x" TyInt))) [TEV "y" (IntEv 4)] [CatEvA (IntEv 4),CatPunc,IntEv 3]