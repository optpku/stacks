/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Polynomial.Numerical.Closure
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Discrete antiderivatives of numerical polynomials

The standard difference operator is mathlib's `fwdDiff`.  This leaf records the numerical-polynomial
antidifference criterion in that language and provides the source-facing predecessor form as a
thin bridge.  No chapter-specific graded or length data is needed here.
-/

@[expose] public section

universe u

open Filter

namespace IsNumericalPolynomial

/-- A function whose unit forward difference is a numerical polynomial is itself a numerical
polynomial. -/
theorem of_fwdDiff_one {A : Type u} [AddCommGroup A] {f : ℤ → A}
    (h : IsNumericalPolynomial (fwdDiff (1 : ℤ) f)) :
    IsNumericalPolynomial f := sorry

/-- Lemma 10.58.5 (Tag 00JZ): an eventual predecessor difference that is a numerical polynomial
has a numerical-polynomial antiderivative. -/
@[stacks 00JZ]
theorem of_sub_pred {A : Type u} [AddCommGroup A] {f : ℤ → A}
    (h : IsNumericalPolynomial (fun n ↦ f n - f (n - 1))) :
    IsNumericalPolynomial f := sorry

end IsNumericalPolynomial
