/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Finiteness.Cardinality
public import ReasLib.LinearAlgebra.Matrix.MinorIdeal.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Presentation Fitting Ideals

@stack 07Z8

This module owns Fitting ideals computed from finite free presentations.  The
intrinsic Fitting ideal of a finite module is defined separately from this
presentation-level construction.
-/

universe u v

section

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The `k`th Fitting ideal computed from a coordinate presentation `π : R^n ⟶ M`.
It is the ideal of `(n - k) × (n - k)` minors of the matrix whose columns are
the kernel vectors of `π`. -/
@[stacks 07Z8 "Fitting ideal of a finite free presentation"]
def presentationFittingIdeal (k : ℕ) {n : ℕ} (π : (Fin n → R) →ₗ[R] M) : Ideal R :=
  Matrix.minorIdeal (n - k) (fun i x ↦ x.1 i : Matrix (Fin n) (LinearMap.ker π) R)

/-- If the Fitting index is at least the rank of the presentation source, its
presentation Fitting ideal is the unit ideal. -/
theorem presentationFittingIdeal_eq_top_of_le {n k : ℕ} (hk : n ≤ k)
    (π : (Fin n → R) →ₗ[R] M) :
    presentationFittingIdeal R M k π = ⊤ := sorry

/-- Surjective finite free presentations determine the same presentation Fitting ideal. -/
@[stacks 07Z8 "presentation independence"]
theorem presentationFittingIdeal_eq_of_surjective {n n' k : ℕ}
    (π : (Fin n → R) →ₗ[R] M) (π' : (Fin n' → R) →ₗ[R] M)
    (hπ : Function.Surjective π) (hπ' : Function.Surjective π') :
    presentationFittingIdeal R M k π = presentationFittingIdeal R M k π' := sorry

/-- Postcomposing a presentation with a linear equivalence preserves its presentation
Fitting ideal. -/
theorem presentationFittingIdeal_comp_linearEquiv {M' : Type*} [AddCommGroup M'] [Module R M']
    (k : ℕ) {n : ℕ} (e : M ≃ₗ[R] M') (π : (Fin n → R) →ₗ[R] M) :
    presentationFittingIdeal R M' k ((e : M →ₗ[R] M').comp π) =
      presentationFittingIdeal R M k π := sorry

end
