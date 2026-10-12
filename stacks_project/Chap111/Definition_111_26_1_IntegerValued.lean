/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import ReasLib.RingTheory.Polynomial.Numerical
import Mathlib.Tactic.CrossRefAttribute

/-!
# Integer-valued rational polynomials

A polynomial over `ℚ` is integer-valued when it sends every integer to an integer.
This is the exercises/tag 027X owner; it is not the eventual binomial-function
predicate `IsNumericalPolynomial` (tag 00JX).
-/

@[expose] public section

namespace Polynomial

/-- A rational polynomial is integer-valued if its evaluation at every integer lies in
the image of `algebraMap ℤ ℚ`. -/
@[stacks 027X]
def IsIntegerValued (f : Polynomial ℚ) : Prop :=
  ∀ n : ℤ, f.eval (algebraMap ℤ ℚ n) ∈ Set.range (algebraMap ℤ ℚ)

/-- Integer-valuedness of a rational polynomial is the existence of an integer value at
every integer argument. -/
theorem isIntegerValued_iff (f : Polynomial ℚ) :
    f.IsIntegerValued ↔
      ∀ n : ℤ, ∃ m : ℤ, f.eval (algebraMap ℤ ℚ n) = algebraMap ℤ ℚ m :=
  sorry

namespace IsIntegerValued

/-- The image of an integer polynomial under `algebraMap ℤ ℚ` is integer-valued. -/
theorem map_int (p : Polynomial ℤ) : (p.map (algebraMap ℤ ℚ)).IsIntegerValued :=
  sorry

/-- An integer-valued rational polynomial has a unique integer-valued evaluation
function on `ℤ`. -/
theorem existsUnique_evalInt {f : Polynomial ℚ} (hf : f.IsIntegerValued) :
    ∃! g : ℤ → ℤ, ∀ n, f.eval (algebraMap ℤ ℚ n) = algebraMap ℤ ℚ (g n) :=
  sorry

/-- The unique integer-valued evaluation of an integer-valued rational polynomial is a
numerical polynomial in the sense of an eventual binomial-basis expansion. -/
theorem isNumericalPolynomial {f : Polynomial ℚ} {g : ℤ → ℤ}
    (hf : f.IsIntegerValued)
    (hg : ∀ n, f.eval (algebraMap ℤ ℚ n) = algebraMap ℤ ℚ (g n)) :
    IsNumericalPolynomial g :=
  sorry

end IsIntegerValued

end Polynomial
