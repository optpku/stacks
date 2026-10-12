/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.Tactic.CrossRefAttribute

/-!
# Powers and rational-function degree

The power formula for `RatFunc.intDegree` is useful in Kummer and purely
inseparable arguments. It is stated for zero as well as nonzero functions;
the zero case is part of the canonical API rather than a caller-side side
condition.

This leaf is shared support for the characteristic-polynomial example in
Chap10 (`@stack 00TY`), not a source-labelled theorem.

@stack 00TY
-/

@[expose] public section

universe u

namespace RatFunc

variable {K : Type u} [Field K]

/-- The degree of a power is the power of the degree, including the zero case. -/
@[simp]
theorem intDegree_pow (x : RatFunc K) (n : ℕ) :
    intDegree (x ^ n) = (n : ℤ) * intDegree x := by
  by_cases hx : x = 0
  · subst x
    cases n <;> simp
  · induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, intDegree_mul (pow_ne_zero n hx) hx, ih]
      push_cast
      ring

/-- For `n > 1`, the rational function `-X` is not an `n`-th power.
The obstruction is its degree at infinity, which equals one. -/
theorem neg_X_not_pow (n : ℕ) (hn : 1 < n) :
    ∀ b : RatFunc K, b ^ n ≠ -(RatFunc.X : RatFunc K) := by
  intro b hb
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_one.trans hn)
  have hb0 : b ≠ 0 := by
    intro h
    subst b
    simp [zero_pow hn0, RatFunc.X_ne_zero] at hb
  have hdegree := congrArg RatFunc.intDegree hb
  have hmul : (n : ℤ) * RatFunc.intDegree b = 1 := by
    simpa [RatFunc.intDegree_pow, RatFunc.intDegree_neg, RatFunc.intDegree_X] using hdegree
  have hdivInt : (n : ℤ) ∣ (1 : ℤ) :=
    ⟨RatFunc.intDegree b, hmul.symm⟩
  have hdivNat : n ∣ 1 := by
    exact_mod_cast hdivInt
  exact (Nat.not_le_of_gt hn) (Nat.le_of_dvd Nat.zero_lt_one hdivNat)

end RatFunc
