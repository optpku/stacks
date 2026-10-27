/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Separated
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.StableDeligneMumford
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.Affine

/-!
# Separatedness of the moduli stack of stable curves of genus `g`

For `2 ≤ g`, the algebraic stack `ℳ̄_g` of stable genus-`g` curves is
separated, meaning that the structure morphism `ℳ̄_g ⟶ Spec(Z)` is
separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- For `2 ≤ g`, the algebraic stack `ℳ̄_g` of stable
genus-`g` curves is separated, i.e. the structure morphism
`ℳ̄_g ⟶ Spec(Z)` is separated. -/
@[stacks 0E9A]
instance _root_.AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instSeparated_stableOfGenus
    (g : ℕ) [Nat.AtLeastTwo g] :
    Separated
      (CohStack.toIdentitySlice (ofObjectProperty (stableOfGenus g specZ))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
