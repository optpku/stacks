/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Polynomial.Numerical
public import ReasLib.RingTheory.Polynomial.Evaluation
public import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.Tactic.CrossRefAttribute

/-!
# Polynomial representatives of numerical polynomials

This neutral leaf converts an integer-indexed binomial-basis expansion to an ordinary polynomial
over a characteristic-zero field.  Rational Hilbert--Samuel uses are specializations and do not
own the representative construction.
-/

@[expose] public section

universe u

namespace IsNumericalPolynomial

/-- A numerical polynomial with values in a characteristic-zero field has a polynomial
representative on the integer tail. -/
@[stacks 00JX "characteristic-zero polynomial representative"]
theorem exists_eventuallyEqInt_polynomial {F : Type u} [Field F] [CharZero F]
    {f : ℤ → F} (hf : IsNumericalPolynomial f) :
    ∃ P : Polynomial F, P.EventuallyEqInt f := sorry

/-- A numerical polynomial with values in a characteristic-zero field has a polynomial
representative on the natural-number tail. -/
@[stacks 00JX "natural-tail polynomial representative"]
theorem exists_eventuallyEqNat_polynomial {F : Type u} [Field F] [CharZero F]
    {f : ℕ → F}
    (hf : IsNumericalPolynomial (fun n : ℤ ↦ f n.toNat)) :
    ∃ P : Polynomial F, P.EventuallyEqNat f := sorry

end IsNumericalPolynomial
