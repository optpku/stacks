/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.Data.Complex.Basic

public section

/-!
# Kähler differentials of multivariable polynomial rings

This file records obstructions to expressing polynomial differential forms in terms of
differentials of specified polynomial generators.
-/

namespace KaehlerDifferential

/-- In `ℂ[X₀, X₁]`, the differential form `2X₀ dX₁` is not a polynomial-linear combination
of `d(X₀²)`, `d(X₀X₁)`, and `d(X₁²)`. -/
theorem mvPolynomial_twoXdy_not_linearCombination :
    ¬ ∃ a b c : MvPolynomial (Fin 2) ℂ,
      ((2 : MvPolynomial (Fin 2) ℂ) * MvPolynomial.X 0) •
          D ℂ (MvPolynomial (Fin 2) ℂ) (MvPolynomial.X 1) =
        a • D ℂ (MvPolynomial (Fin 2) ℂ) (MvPolynomial.X 0 ^ 2) +
        b • D ℂ (MvPolynomial (Fin 2) ℂ) (MvPolynomial.X 0 * MvPolynomial.X 1) +
        c • D ℂ (MvPolynomial (Fin 2) ℂ) (MvPolynomial.X 1 ^ 2) := sorry

end KaehlerDifferential
