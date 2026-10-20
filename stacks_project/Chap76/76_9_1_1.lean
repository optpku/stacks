/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
