module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Thickening

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- 76.9.1.1: if `i : X ⟶ X'` is a thickening of algebraic spaces, the
spaces-étale sites are identified via `spacesEtalePullback`, i.e.
`X_spaces,étale = X'_spaces,étale`. -/
@[stacks 05ZL] #check
  (AlgebraicGeometry.AlgebraicSpace.spacesEtalePullback_isEquivalence_of_isThickening :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X') [IsThickening i],
      (spacesEtalePullback i).IsEquivalence)
