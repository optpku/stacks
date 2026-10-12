/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Regular.RegularSequence

@[expose] public section

universe u

open IsLocalRing RingTheory.Sequence

/-- In a Noetherian local ring, if `x, y` lie in the maximal ideal and form a
regular sequence, then `x ^ (n - 1) * y ^ (n - 1)` does not belong to
`Ideal.span {x ^ n, y ^ n}` for `n ≥ 2`. -/
theorem RingTheory.Sequence.IsRegular.pow_mul_pow_notMem_span_pow {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {x y : R} (hx : x ∈ maximalIdeal R) (hy : y ∈ maximalIdeal R)
    (hxy : IsRegular R [x, y]) {n : ℕ} (hn : 2 ≤ n) :
    x ^ (n - 1) * y ^ (n - 1) ∉ Ideal.span {x ^ n, y ^ n} := sorry

/-- In a Noetherian local ring, a length-2 regular sequence `x, y` in the maximal
ideal admits no coefficients `a, b` with `x ^ (n - 1) * y ^ (n - 1) = a * x ^ n + b * y ^ n`
for `n ≥ 2`. -/
theorem RingTheory.Sequence.IsRegular.not_exists_eq_mul_pow_add_mul_pow {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {x y : R} (hx : x ∈ maximalIdeal R) (hy : y ∈ maximalIdeal R)
    (hxy : IsRegular R [x, y]) {n : ℕ} (hn : 2 ≤ n) :
    ¬ ∃ a b : R, x ^ (n - 1) * y ^ (n - 1) = a * x ^ n + b * y ^ n := sorry
