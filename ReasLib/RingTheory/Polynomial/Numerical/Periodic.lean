/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Polynomial.Numerical.Closure
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Eventually quasi-polynomial functions

This leaf owns the residue-class formulation used by Veronese and quasi-polynomial arguments.  It
does not mention graded rings or modules, so those developments can reuse the predicate directly.
-/

@[expose] public section

universe u

open Filter

variable {A : Type u} [AddCommGroup A]

/-
API design: a positive natural period is bundled as `ℕ+`, while residues use `Fin (n : ℕ)` and the
progression is written explicitly as `a + n * q` in `ℤ`.  This keeps the definition faithful to the
integer-indexed numerical-polynomial owner and avoids a second quotient/index type.
-/

/-- A function on `ℤ` is eventually quasi-polynomial when every residue-class slice is eventually
equal to a numerical polynomial. -/
def EventuallyQuasiPolynomial (f : ℤ → A) : Prop :=
  ∃ n : ℕ+, ∀ a : Fin (n : ℕ), ∃ g : ℤ → A,
    IsNumericalPolynomial g ∧
      (fun q : ℤ => f (((a : ℕ) : ℤ) + (((n : ℕ) : ℤ) * q))) =ᶠ[atTop] g

/-- A numerical polynomial is eventually quasi-polynomial with period `1`. -/
theorem IsNumericalPolynomial.eventuallyQuasiPolynomial {f : ℤ → A}
    (hf : IsNumericalPolynomial f) : EventuallyQuasiPolynomial f := sorry

/-- Residue-class numerical polynomials assemble into an eventually quasi-polynomial. -/
theorem EventuallyQuasiPolynomial.ofResidueSlices
    {f : ℤ → A} {n : ℕ+}
    (h : ∀ a : Fin (n : ℕ), ∃ g : ℤ → A,
      IsNumericalPolynomial g ∧
        (fun q : ℤ => f (((a : ℕ) : ℤ) + (((n : ℕ) : ℤ) * q))) =ᶠ[atTop] g) :
    EventuallyQuasiPolynomial f := sorry
