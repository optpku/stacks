/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Prime

@[expose] public section

namespace Ideal

/-- If `a * b = 0`, `a ∉ J`, and `b ∉ I`, no prime ideal is contained in both
`I` and `J`. -/
theorem not_exists_prime_le_of_mul_eq_zero
    (R : Type*) [CommRing R] (a b : R) (I J : Ideal R)
    (h_mul_eq_zero : a * b = 0) (h_not_mem_right : a ∉ J) (h_not_mem_left : b ∉ I) :
    ¬ ∃ p : Ideal R, p.IsPrime ∧ p ≤ I ∧ p ≤ J := sorry

end Ideal
