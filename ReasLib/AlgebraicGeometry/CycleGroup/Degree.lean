/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.FiniteType

/-!
# Degrees of zero-cycles

This module defines the degree of a relative zero-cycle on a proper scheme over a field and
expresses it as a sum of residue-field degrees.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

variable {k : Type u} [Field k]

/-- Evaluation at the unique point of `Spec k` after pushforward along the structure morphism
preserves addition of relative zero-cycles. -/
theorem mapToBase_apply_add (X : SchemeOverField k) [IsProper X.hom]
    (α β : CycleGroup X.left
      (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ 0)) 0) :
    toAlgebraicCycle (fun _ : Spec (CommRingCat.of k) ↦ 0) 0
        (mapHom X.hom (X.hom.relativeDimensionFunction
          (fun _ : Spec (CommRingCat.of k) ↦ 0))
          (fun _ : Spec (CommRingCat.of k) ↦ 0) 0 (α + β)) default =
      toAlgebraicCycle (fun _ : Spec (CommRingCat.of k) ↦ 0) 0
          (mapHom X.hom (X.hom.relativeDimensionFunction
            (fun _ : Spec (CommRingCat.of k) ↦ 0))
            (fun _ : Spec (CommRingCat.of k) ↦ 0) 0 α) default +
        toAlgebraicCycle (fun _ : Spec (CommRingCat.of k) ↦ 0) 0
          (mapHom X.hom (X.hom.relativeDimensionFunction
            (fun _ : Spec (CommRingCat.of k) ↦ 0))
            (fun _ : Spec (CommRingCat.of k) ↦ 0) 0 β) default := sorry

/-- The degree of a relative zero-cycle on a proper scheme over a field, obtained by
pushforward to `Spec k` and evaluation at its unique point. -/
noncomputable def degree (X : SchemeOverField k) [IsProper X.hom] :
    CycleGroup X.left
        (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ 0)) 0 →+ ℤ :=
  AddMonoidHom.mk'
    (fun α ↦
      toAlgebraicCycle (fun _ : Spec (CommRingCat.of k) ↦ 0) 0
        (mapHom X.hom (X.hom.relativeDimensionFunction
          (fun _ : Spec (CommRingCat.of k) ↦ 0))
          (fun _ : Spec (CommRingCat.of k) ↦ 0) 0 α) default)
    (mapToBase_apply_add X)

/-- The degree of a relative zero-cycle is the finite sum of its coefficients weighted by
residue-field degrees over the base field. -/
theorem degree_eq_finsum_residueDegree (X : SchemeOverField k) [IsProper X.hom]
    (α : CycleGroup X.left
      (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ 0)) 0) :
    degree X α = ∑ᶠ x : X.left,
      toAlgebraicCycle (X.hom.relativeDimensionFunction
        (fun _ : Spec (CommRingCat.of k) ↦ 0)) 0 α x *
        (X.hom.residueDegree x : ℤ) := sorry

end AlgebraicGeometry.CycleGroup
