module

import StacksCheckRecall
import stacks_project.Chap76.«76_9_1_1_Equivalence»

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- 76.9.1.1: if `i : X ⟶ X'` is a thickening of algebraic spaces, the
spaces-étale sites are identified via `spacesEtalePullback`, i.e.
`X_spaces,étale = X'_spaces,étale`. -/
@[stacks 05ZL] #check
  (spacesEtalePullback_isEquivalence_of_isThickening :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X') [IsThickening i],
      (spacesEtalePullback i).IsEquivalence)
