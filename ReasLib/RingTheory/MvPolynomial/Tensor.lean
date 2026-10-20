/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coefficient coordinates of polynomial tensor products

This leaf names the coefficient-coordinate equivalence for a tensor product of a multivariable
polynomial module with an arbitrary module.  The carrier is owned by Mathlib's
`TensorProduct.finsuppScalarLeft`; this namespace only gives the polynomial spelling and its
pointwise computation rule.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v

namespace MvPolynomial

variable {R : Type u} [CommSemiring R]
variable {N : Type v} [AddCommMonoid N] [Module R N]
variable {σ : Type*}

/-- Stacks `061P`: expand a polynomial tensor into its coefficient family in `N`.

The definition is a direct alias of `TensorProduct.finsuppScalarLeft`, so it introduces no second
tensor or coefficient representation. -/
@[stacks 061P "polynomial tensor coefficient equivalence"]
noncomputable def scalarRTensor (R : Type u) (N : Type v) (σ : Type*)
    [CommSemiring R] [AddCommMonoid N] [Module R N] :
    MvPolynomial σ R ⊗[R] N ≃ₗ[R] (σ →₀ ℕ) →₀ N :=
  by
    classical
    exact
      (TensorProduct.congr (AddMonoidAlgebra.coeffLinearEquiv R)
        (LinearEquiv.refl R N)).trans
        (TensorProduct.finsuppScalarLeft R N (σ →₀ ℕ))

/-- Stacks `061P`: the coefficient coordinate of a pure polynomial tensor is scalar multiplication
by the corresponding polynomial coefficient. -/
@[simp, stacks 061P "polynomial tensor coefficient formula"]
theorem scalarRTensor_apply_tmul_apply (p : MvPolynomial σ R) (n : N)
    (e : σ →₀ ℕ) :
    scalarRTensor R N σ (p ⊗ₜ[R] n) e = p.coeff e • n := sorry

/-- Stacks `061P`: the inverse coefficient coordinate of a single-support family is the
corresponding unit-coefficient monomial tensor. -/
@[stacks 061P "inverse polynomial tensor coefficient formula"]
theorem scalarRTensor_symm_apply_single (e : σ →₀ ℕ) (n : N) :
    (scalarRTensor R N σ).symm (Finsupp.single e n) =
      MvPolynomial.monomial e (1 : R) ⊗ₜ[R] n := sorry

/-- Stacks `061P`: the coefficient expansion is injective. -/
@[stacks 061P "injectivity of polynomial tensor coefficient expansion"]
theorem scalarRTensor_injective : Function.Injective (scalarRTensor R N σ) := sorry

end MvPolynomial

namespace TensorProduct

variable {R : Type u} [CommSemiring R]
variable {N : Type v} [AddCommMonoid N] [Module R N]
variable {σ : Type*}

/-!
The finite-support normal form below is stated in the tensor orientation used by source-facing
graded constructions (`N ⊗ MvPolynomial`).  The coefficient family is concrete `Finsupp` data;
the existence proposition does not choose a second tensor carrier.
-/

/-- Stacks `061P`: every tensor with a multivariable polynomial factor is a finite sum of
unit-coefficient monomial pure tensors. -/
@[stacks 061P "finite monomial expansion of a polynomial tensor"]
theorem exists_sum_tmul_monomial
    (z : N ⊗[R] MvPolynomial σ R) :
    ∃ coeffs : (σ →₀ ℕ) →₀ N,
      z = coeffs.sum fun e n ↦ n ⊗ₜ[R] MvPolynomial.monomial e (1 : R) := sorry

end TensorProduct

end
