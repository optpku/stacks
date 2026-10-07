module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Homogeneous p-th-power kernels

This module defines the homogeneous two-variable p-th-power relation and its quotient
coordinate ring.
-/

@[expose] public section

noncomputable section

universe u v

namespace MvPolynomial.PthPowerKernel

/-- The homogeneous polynomial `X₀ ^ p + α * X₁ ^ p`. -/
def relation {k : Type u} [CommRing k] (p : ℕ) (α : k) :
    MvPolynomial (ULift.{u} (Fin 2)) k :=
  X (ULift.up (0 : Fin 2)) ^ p + C α * X (ULift.up (1 : Fin 2)) ^ p

/-- Evaluating `relation p α` gives the equation `x₀ ^ p + α * x₁ ^ p`. -/
theorem eval_relation {k : Type u} [CommRing k] {A : Type v} [CommRing A]
    (f : k →+* A) (x : ULift.{u} (Fin 2) → A) (p : ℕ) (α : k) :
    eval₂ f x (relation p α) =
      x (ULift.up (0 : Fin 2)) ^ p + f α * x (ULift.up (1 : Fin 2)) ^ p := by
  simp [relation]

/-- The coordinate ring cut out by `relation p α`. -/
abbrev Ring {k : Type u} [CommRing k] (p : ℕ) (α : k) :=
  MvPolynomial (ULift.{u} (Fin 2)) k ⧸
    Ideal.span ({relation p α} : Set (MvPolynomial (ULift.{u} (Fin 2)) k))

/-- The defining relation vanishes in `Ring p α`. -/
theorem quotient_relation_eq_zero {k : Type u} [CommRing k] (p : ℕ) (α : k) :
    Ideal.Quotient.mk (Ideal.span ({relation p α} : Set (MvPolynomial (ULift.{u} (Fin 2)) k)))
      (relation p α) = (0 : Ring p α) := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

/-- If `α` is not a p-th power, the coordinate ring of the homogeneous kernel is a domain. -/
theorem isDomain (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
    (α : k) (hα : α ∉ Set.range (fun β : k ↦ β ^ p)) :
    IsDomain (Ring p α) := sorry

end MvPolynomial.PthPowerKernel
