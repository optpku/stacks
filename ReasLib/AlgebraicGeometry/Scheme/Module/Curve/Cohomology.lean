module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

/-!
# Cohomology of invertible modules on proper curves

This file records existence results for invertible modules with prescribed low-degree
cohomology on proper curves over algebraically closed fields.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : Over (Spec (CommRingCat.of k))) [Curve X] [IsProper X.hom]

/-- A proper curve over an algebraically closed field has an invertible module whose
degree-zero cohomology has dimension one and whose degree-one cohomology vanishes. -/
@[stacks 0B8Z]
theorem exists_invertible_with_h0_finrank_one_h1_zero :
    ∃ (ℒ : X.left.Modules) (hℒ : Invertible ℒ),
      let _ : Invertible ℒ := hℒ
      Scheme.Hom.cohomologyFinrank X.hom ℒ 0 = 1 ∧
        IsZero (Scheme.Modules.cohomology ℒ 1) := sorry

/-- A proper curve over an algebraically closed field has an invertible module whose
degree-zero and degree-one cohomology both vanish. -/
@[stacks 0B8Z]
theorem exists_invertible_with_h0_finrank_zero_h1_zero :
    ∃ (𝒩 : X.left.Modules) (h𝒩 : Invertible 𝒩),
      let _ : Invertible 𝒩 := h𝒩
      Scheme.Hom.cohomologyFinrank X.hom 𝒩 0 = 0 ∧
        IsZero (Scheme.Modules.cohomology 𝒩 1) := sorry

end

end AlgebraicGeometry.Scheme.Modules
