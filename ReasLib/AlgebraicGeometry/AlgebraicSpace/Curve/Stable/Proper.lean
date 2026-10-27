/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.StableSeparated

/-!
# Properness of the moduli stack of stable curves

The canonical structure morphism of stable genus-`g` curves is proper over
`Spec ℤ` for `g ≥ 2`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack.Hom renaming Proper → GroupoidProper
open scoped Bicategory

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- For `g ≥ 2`, the canonical structure morphism of the stack of stable
genus-`g` curves to `Spec ℤ` is proper. -/
instance instProper_stableOfGenus (g : ℕ) [Nat.AtLeastTwo g] :
    GroupoidProper
      (CohStack.toIdentitySlice (ofObjectProperty (stableOfGenus g specZ))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
