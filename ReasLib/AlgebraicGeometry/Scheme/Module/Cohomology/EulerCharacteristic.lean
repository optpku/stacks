/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.EulerCharacteristic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections

/-!
# Euler characteristics over a field

This leaf owns the Euler characteristic of a coherent scheme module on a
scheme proper over a field.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k]
variable {X : Scheme.{u}}

/-- The Euler characteristic of a coherent module on a scheme proper over a field, defined as
the signed finite sum of the dimensions of its cohomology groups. -/
@[stacks 0BEJ]
noncomputable def eulerCharacteristic
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] : ℤ :=
  GradedObject.eulerChar (ComplexShape.up ℕ)
    (fun i : ℕ => cohomology f F i)

/-- Unfold the Euler characteristic into the signed finite sum of cohomology dimensions. -/
@[stacks 0BEJ]
theorem eulerCharacteristic_def
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] :
    eulerCharacteristic f F =
      ∑ᶠ i : ℕ,
        ((i : ℤ).negOnePow : ℤ) * (cohomologyFinrank f F i : ℤ) := sorry

/-- The Euler characteristic is additive along a short exact complex of coherent modules on a
scheme proper over a field. -/
@[stacks 08AA]
theorem eulerCharacteristic_eq_add_of_shortExact
    {S : ShortComplex X.Modules}
    [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (hS : S.ShortExact) :
    eulerCharacteristic f S.X₂ =
      eulerCharacteristic f S.X₁ + eulerCharacteristic f S.X₃ := sorry

end AlgebraicGeometry.Scheme.Hom
