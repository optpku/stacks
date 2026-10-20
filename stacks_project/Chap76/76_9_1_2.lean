/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.RingedTopos

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Thickening

universe u

/- 76.9.1.2: if `i : X ⟶ X'` is a thickening of algebraic spaces, the
spaces-étale sites are identified by 76.9.1.1, so `𝒪_{X'}` may be viewed on
`X_spaces,étale`. This yields a canonical equivalence of locally ringed topoi
`(Sh(X'_spaces,étale), 𝒪_{X'}) ≅ (Sh(X_spaces,étale), 𝒪_{X'})` via
`closedRingedToposHom`. -/
@[stacks 05ZM] #check
  (AlgebraicGeometry.AlgebraicSpace.Thickening.closedRingedToposHom_isEquivalence_of_isThickening :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X') [IsThickening i],
      (AlgebraicGeometry.AlgebraicSpace.Thickening.closedRingedToposHom i).IsEquivalence)
