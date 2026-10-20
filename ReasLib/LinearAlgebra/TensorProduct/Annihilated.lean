/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Scalar extension of modules annihilated by an ideal

For an ideal acting by zero, quotient scalar extension has its canonical inverse
given by scalar multiplication: `[r] ⊗ m ↦ r • m`.
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace TensorProduct

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- An ideal acting by zero generates the zero submodule. -/
theorem ideal_smul_top_eq_bot (I : Ideal R) (hI : ∀ r ∈ I, ∀ m : M, r • m = 0) :
    I • (⊤ : Submodule R M) = ⊥ := by
  apply le_antisymm
  · apply Submodule.smul_le.mpr
    intro r hr m _
    exact (Submodule.mem_bot R).mpr (hI r hr m)
  · exact bot_le

/-- Extending scalars to `R/I` preserves a module annihilated by `I`.
Both maps are the native tensor-quotient and quotient-descent maps. -/
noncomputable def quotientTensorEquivOfAnnihilated
    (I : Ideal R) (hI : ∀ r ∈ I, ∀ m : M, r • m = 0) :
    ((R ⧸ I) ⊗[R] M) ≃ₗ[R] M :=
  (quotTensorEquivQuotSMul M I).trans
    ((I • (⊤ : Submodule R M)).quotEquivOfEqBot (ideal_smul_top_eq_bot I hI))

/-- The scalar-extension comparison sends `[r] ⊗ m` to `r • m`. -/
@[simp]
theorem quotientTensorEquivOfAnnihilated_mk_tmul
    (I : Ideal R) (hI : ∀ r ∈ I, ∀ m : M, r • m = 0) (r : R) (m : M) :
    quotientTensorEquivOfAnnihilated I hI (Ideal.Quotient.mk I r ⊗ₜ[R] m) = r • m := by
  simp [quotientTensorEquivOfAnnihilated, quotTensorEquivQuotSMul_mk_tmul]

/-- The inverse comparison sends a section to `1 ⊗ m`. -/
@[simp]
theorem quotientTensorEquivOfAnnihilated_symm_apply
    (I : Ideal R) (hI : ∀ r ∈ I, ∀ m : M, r • m = 0) (m : M) :
    (quotientTensorEquivOfAnnihilated I hI).symm m =
      (1 : R ⧸ I) ⊗ₜ[R] m := by
  apply (quotientTensorEquivOfAnnihilated I hI).injective
  simp [quotientTensorEquivOfAnnihilated]

end TensorProduct
