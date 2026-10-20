module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Length
public import ReasLib.RingTheory.Localization.TotalQuotient
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Normalization Quotients

This module names the total-quotient-ring normalization of an arbitrary commutative ring,
its quotient by the original ring, and the resulting length invariant.
-/

universe u

open scoped nonZeroDivisors

namespace Normalization

variable (R : Type u) [CommRing R]

/-- The integral closure of `R` in its total quotient ring. -/
abbrev normalizationRing : Subalgebra R (Localization.totalQuotientRing R) :=
  _root_.integralClosure R (Localization.totalQuotientRing R)

/-- The quotient module of the normalization of `R` by the image of `R`. -/
abbrev quotient : Type u :=
  normalizationRing R ⧸ (Algebra.linearMap R (normalizationRing R)).range

/-- Compute the normalization quotient as the quotient of the integral closure in the total
quotient ring by the image of `R`. -/
@[simp]
theorem quotient_def :
    quotient R =
      (normalizationRing R ⧸ (Algebra.linearMap R (normalizationRing R)).range) := sorry

/-- The length of the normalization quotient of a commutative ring. This invariant is defined
without hypotheses that ensure finiteness or give it a geometric interpretation. -/
@[stacks 0C3T]
noncomputable abbrev deltaInvariant : ℕ∞ := Module.length R (quotient R)

/-- Compute the normalization `δ`-invariant as the length of the normalization quotient. -/
@[simp]
theorem deltaInvariant_def :
    deltaInvariant R = Module.length R (quotient R) := sorry

end Normalization
