module

public import stacks_project.Chap66.Lemma_66_18_8_Pullback
public import stacks_project.Chap76.Lemma_76_9_2_Thickening

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a thickening `i : X ⟶ X'` of algebraic spaces, base change along `i`
induces an equivalence from the spaces-étale site of `X'` to the spaces-étale
site of `X`. -/
instance spacesEtalePullback_isEquivalence_of_isThickening
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X') [IsThickening i] :
    (spacesEtalePullback i).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicSpace
