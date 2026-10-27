/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.StableSeparated

open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/- Lemma 109.25.1: For `2 ≤ g`, the algebraic stack of stable genus-`g`
curves is separated over `Spec ℤ`. -/
@[stacks 0E9A] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instSeparated_stableOfGenus :
    ∀ (g : ℕ) [Nat.AtLeastTwo g],
      CohStack.Hom.Separated
        (CohStack.toIdentitySlice (ofObjectProperty (stableOfGenus g specZ))))
