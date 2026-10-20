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

/- Lemma 76.9.6: if `i : X ⟶ X'` is a thickening of algebraic spaces over a
scheme `S`, the functor `V' ↦ X ×_{X'} V'` defines an equivalence of categories
`X'_étale ⥤ X_étale`. -/
@[stacks 05ZS] #check
  (@AlgebraicGeometry.AlgebraicSpace.smallEtalePullback.isEquivalence_of_isThickening :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X') [IsThickening i]
      (hf : yoneda.relativelyRepresentable i),
      (smallEtalePullback i hf).IsEquivalence)
