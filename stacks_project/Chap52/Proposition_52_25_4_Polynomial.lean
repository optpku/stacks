/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Polynomial.Numerical
import Mathlib.Order.WithBot

@[expose] public section

open Filter

universe u

open scoped BigOperators

namespace AlgebraicGeometry

/-- A numerical polynomial whose eventual binomial expansion has degree at most `d`.

The bottom bound records the empty-support case: at degree `⊥`, the function is eventually
constant. For a non-bottom bound, the finite binomial expansion is required to have a natural
degree whose cast to `WithBot ℕ∞` is bounded by `d`. -/
def IsNumericalPolynomialOfDegreeLE (f : ℤ → ℤ) (d : WithBot ℕ∞) : Prop :=
  (d = (⊥ : WithBot ℕ∞) ∧ ∃ c : ℤ, f =ᶠ[Filter.atTop] fun _ ↦ c) ∨
    ∃ r : ℕ, (r : WithBot ℕ∞) ≤ d ∧ IsNumericalPolynomial.hasExpansion f r

namespace IsNumericalPolynomialOfDegreeLE

/-- A degree-bounded numerical polynomial is a numerical polynomial. -/
theorem isNumericalPolynomial {f : ℤ → ℤ} {d : WithBot ℕ∞}
    (hf : IsNumericalPolynomialOfDegreeLE f d) : IsNumericalPolynomial f := sorry

/-- Degree-bounded numerical polynomiality is preserved by eventual equality. -/
theorem congr {f g : ℤ → ℤ} {d : WithBot ℕ∞}
    (hf : IsNumericalPolynomialOfDegreeLE f d) (hfg : f =ᶠ[Filter.atTop] g) :
    IsNumericalPolynomialOfDegreeLE g d := sorry

/-- The bottom degree bound is exactly eventual constancy. -/
theorem bot_iff {f : ℤ → ℤ} :
    IsNumericalPolynomialOfDegreeLE f (⊥ : WithBot ℕ∞) ↔
      ∃ c : ℤ, f =ᶠ[Filter.atTop] fun _ ↦ c := sorry

end IsNumericalPolynomialOfDegreeLE

end AlgebraicGeometry
