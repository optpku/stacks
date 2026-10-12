/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic

@[expose] public section

open scoped TensorProduct

/-!
# Left tensor maps for exterior powers

@stack 052U

This file provides the canonical map which prepends a mapped factor to an exterior power.
-/

namespace exteriorPower

universe u v w

section

variable {R : Type u} [CommRing R]
variable {M₂ : Type v} [AddCommGroup M₂] [Module R M₂]
variable {M₁ : Type w} [AddCommGroup M₁] [Module R M₁]

/-- The canonical map `M₂ ⊗[R] ⋀[R]^n M₁ → ⋀[R]^(n + 1) M₁` induced by `f`. -/
noncomputable def leftTensorMap (n : ℕ) (f : M₂ →ₗ[R] M₁) :
    M₂ ⊗[R] ⋀[R]^n M₁ →ₗ[R] ⋀[R]^(n + 1) M₁ :=
  TensorProduct.lift {
    toFun := fun x ↦ alternatingMapLinearEquiv ((ιMulti R (n + 1)).curryLeft (f x))
    map_add' x y := by
      ext m
      simp
    map_smul' r x := by
      ext m
      simp
  }

/-- `exteriorPower.leftTensorMap` on pure exterior tensors. -/
@[simp]
theorem leftTensorMap_tmul_ιMulti (n : ℕ) (f : M₂ →ₗ[R] M₁)
    (x : M₂) (m : Fin n → M₁) :
    leftTensorMap n f (x ⊗ₜ exteriorPower.ιMulti R n m) =
      exteriorPower.ιMulti R (n + 1) (Fin.cons (f x) m) := sorry

/-- The canonical map that wedges a module element on the left is surjective onto the next
exterior-power degree. -/
@[stacks 052U]
theorem leftTensorMap_id_surjective (n : ℕ) :
    Function.Surjective (leftTensorMap n (LinearMap.id : M₁ →ₗ[R] M₁)) := sorry

/-- The `R`-linear map which wedges a fixed element on the left of a homogeneous exterior form.

This is the specialization of `leftTensorMap` to the identity map on the left factor. -/
noncomputable def leftWedge (x : M₁) (n : ℕ) :
    ⋀[R]^n M₁ →ₗ[R] ⋀[R]^(n + 1) M₁ :=
  leftTensorMap n (LinearMap.id : M₁ →ₗ[R] M₁) ∘ₗ
    TensorProduct.mk R M₁ (⋀[R]^n M₁) x

/-- `exteriorPower.leftWedge` prepends its fixed factor to an exterior-power generator. -/
@[simp]
theorem leftWedge_apply_ιMulti (x : M₁) (n : ℕ) (m : Fin n → M₁) :
    leftWedge x n (exteriorPower.ιMulti R n m) =
      exteriorPower.ιMulti R (n + 1) (Fin.cons x m) := sorry

/-- The degree-two left wedge map with a fixed first factor and an unbundled second factor.

This uses the canonical identification `M ≃ₗ[R] ⋀[R]^1 M` before applying `leftWedge`. -/
noncomputable def leftWedgeOne (x : M₁) : M₁ →ₗ[R] ⋀[R]^2 M₁ :=
  (leftWedge x 1).comp (oneEquiv R M₁).symm.toLinearMap

/-- `exteriorPower.leftWedgeOne` evaluates to the basic two-form with its factors in order. -/
@[simp]
theorem leftWedgeOne_apply (x y : M₁) :
    leftWedgeOne x y =
      exteriorPower.ιMulti R 2 (Fin.cases x fun _ ↦ y) := sorry

end

end exteriorPower
