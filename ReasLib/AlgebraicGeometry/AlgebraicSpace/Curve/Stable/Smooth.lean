/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.StructureMorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.StableDeligneMumford

/-!
# Smoothness of the moduli stacks of stable curves

The structure morphisms of the stable locus and its genus-`g` locus, for `2 ≤ g`,
are smooth over any base scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack.Hom renaming Smooth → GroupoidSmooth
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The structure morphism of the stack of stable curves over a scheme is smooth. -/
@[stacks 0E79]
instance instSmooth_stable (S : Scheme.{u}) :
    GroupoidSmooth
      (inclusionOf (stable S) ≫ CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

/-- For `2 ≤ g`, the structure morphism of the stack of stable curves of genus `g`
over a scheme is smooth. -/
@[stacks 0E79]
instance instSmooth_stableOfGenus (g : ℕ) (S : Scheme.{u}) [Fact (2 ≤ g)] :
    GroupoidSmooth
      (inclusionOf (stableOfGenus g S) ≫
        CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

/-- For `g ≥ 2`, the canonical structure morphism of the stack of stable
genus-`g` curves over any scheme is smooth. -/
instance instSmooth_toIdentitySlice_stableOfGenus
    (g : ℕ) [Nat.AtLeastTwo g] (S : Scheme.{u}) :
    GroupoidSmooth
      (CohStack.toIdentitySlice (ofObjectProperty (stableOfGenus g S))) := by
  rw [CohStack.toIdentitySlice_comp (inclusionOf (stableOfGenus g S))]
  exact @instSmooth_stableOfGenus g S ⟨Nat.AtLeastTwo.prop⟩

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
