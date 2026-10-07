module

public import stacks_project.Chap66.Lemma_66_18_8_Representable
public import stacks_project.Chap76.Lemma_76_9_2_Thickening

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a thickening `i : X ⟶ X'` of algebraic spaces, base change along `i`
induces an equivalence from the small étale site of `X'` to the small étale
site of `X`. -/
instance smallEtalePullback.isEquivalence_of_isThickening
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X') [IsThickening i]
    (hf : yoneda.relativelyRepresentable i) :
    (smallEtalePullback i hf).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicSpace
