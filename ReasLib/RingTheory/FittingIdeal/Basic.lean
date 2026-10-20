/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.FittingIdeal.Presentation
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Intrinsic Fitting Ideals

@stack 07Z9

This module defines the intrinsic Fitting ideals of finite modules from the
presentation-level construction and records their primary comparison API.
-/

universe u v w

section

variable (R : Type u) [CommRing R]

/-- The convention for the Fitting ideal in index `-1`: it is the zero ideal. -/
@[stacks 07Z9 "negative-one Fitting ideal"]
abbrev fittingIdealNegOne : Ideal R :=
  (⊥ : Ideal R)

/-- The negative-one Fitting ideal is the zero ideal. -/
@[simp]
theorem fittingIdealNegOne_eq_bot :
    fittingIdealNegOne R = (⊥ : Ideal R) := sorry

end

section

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- A surjective presentation of `M` by a finite coordinate free module.
This type is allowed to be empty when `M` is not finite. -/
@[stacks 07Z9 "surjective finite free presentation of a module"]
abbrev SurjectivePresentation :=
  Σ n : ℕ, { π : (Fin n → R) →ₗ[R] M // Function.Surjective π }

/- The empty-presentation convention makes the data owner total: if `M` has no
finite free surjection, the infimum below is `⊤`. All mathematical comparison
theorems retain the finiteness hypotheses under which the usual Fitting ideal
is recovered. -/

/-- The `k`th intrinsic Fitting ideal of an `R`-module, computed as the infimum
of the ideals attached to all its surjective finite free presentations. -/
@[stacks 07Z9 "intrinsic Fitting ideal"]
def fittingIdeal : ℕ → Ideal R := fun k ↦
  sInf <| Set.range fun P : SurjectivePresentation R M ↦ presentationFittingIdeal R M k P.2.1

namespace FittingIdeal

/-! Textbook notation for intrinsic Fitting ideals. -/
scoped notation "Fit[" R "]_(" k ")(" M ")" => fittingIdeal R M k

end FittingIdeal

open scoped FittingIdeal

/-- The Fitting ideal one step below `Fit_r(M)`, with the convention
`Fit_{-1}(M) = 0`. -/
@[stacks 07Z9 "preceding Fitting ideal"]
abbrev precedingFittingIdeal (r : ℕ) : Ideal R :=
  if r = 0 then fittingIdealNegOne R else Fit[R]_(r - 1)(M)

/-- The predecessor of the zeroth Fitting ideal is the zero ideal. -/
@[simp]
theorem precedingFittingIdeal_zero :
    precedingFittingIdeal R M 0 = ⊥ := sorry

/-- The predecessor of `Fit_{r + 1}(M)` is `Fit_r(M)`. -/
@[simp]
theorem precedingFittingIdeal_succ (r : ℕ) :
    precedingFittingIdeal R M (r + 1) = Fit[R]_(r)(M) := sorry

/-- The intrinsic Fitting ideal agrees with the ideal computed from any
surjective finite free presentation. -/
@[stacks 07Z9 "intrinsic and presentation Fitting ideals"]
theorem fittingIdeal_eq_presentationFittingIdeal (k : ℕ) {n : ℕ}
    (π : (Fin n → R) →ₗ[R] M) (hπ : Function.Surjective π) :
    Fit[R]_(k)(M) = presentationFittingIdeal R M k π := sorry

/-- The intrinsic Fitting ideal is the ideal of minors of any relation matrix
whose columns span the kernel of a surjective finite free presentation. -/
theorem fittingIdeal_eq_minorIdeal_of_span_eq_ker (k : ℕ) {n : ℕ} {J : Type w}
    (π : (Fin n → R) →ₗ[R] M) (hπ : Function.Surjective π)
    (A : Matrix (Fin n) J R)
    (hA : Submodule.span R (Set.range (fun j => fun i => A i j)) = LinearMap.ker π) :
    fittingIdeal R M k = Matrix.minorIdeal (n - k) A := sorry

/-- Intrinsic Fitting ideals are preserved by a linear equivalence when both
modules are given as finite modules. -/
theorem fittingIdeal_eq_of_linearEquiv_of_finite [Module.Finite R M]
    {M' : Type w} [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    (k : ℕ) (e : M ≃ₗ[R] M') :
    Fit[R]_(k)(M) = Fit[R]_(k)(M') := sorry

/-- Intrinsic Fitting ideals are invariant under linear equivalence of finite modules. -/
theorem fittingIdeal_eq_of_linearEquiv [Module.Finite R M]
    {M' : Type w} [AddCommGroup M'] [Module R M'] (k : ℕ) (e : M ≃ₗ[R] M') :
    Fit[R]_(k)(M) = Fit[R]_(k)(M') := sorry

end
