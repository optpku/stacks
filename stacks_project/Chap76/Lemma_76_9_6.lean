module

import StacksCheckRecall
import stacks_project.Chap76.Lemma_76_9_6_Equivalence

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.9.6: if `i : X ⟶ X'` is a thickening of algebraic spaces over a
scheme `S`, the functor `V' ↦ X ×_{X'} V'` defines an equivalence of categories
`X'_étale ⥤ X_étale`. -/
@[stacks 05ZS] #check
  (smallEtalePullback.isEquivalence_of_isThickening :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X') [IsThickening i]
      (hf : yoneda.relativelyRepresentable i),
      (smallEtalePullback i hf).IsEquivalence)
