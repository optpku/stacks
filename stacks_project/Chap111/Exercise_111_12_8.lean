/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Sequence.Regularity.Monomial
import StacksCheckRecall

@[expose] public section

universe u

open IsLocalRing RingTheory.Sequence

/- Exercise 111.12.8: in a Noetherian local ring `R`, if `x, y ∈ maximalIdeal R`
form a regular sequence of length 2, then for every `n ≥ 2` the monomial
`x ^ (n - 1) * y ^ (n - 1)` does not lie in `Ideal.span {x ^ n, y ^ n}`. -/
@[stacks 0CT2] #check (RingTheory.Sequence.IsRegular.pow_mul_pow_notMem_span_pow :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {x y : R}
      (hx : x ∈ maximalIdeal R) (hy : y ∈ maximalIdeal R)
      (hxy : IsRegular R [x, y]) {n : ℕ} (hn : 2 ≤ n),
      x ^ (n - 1) * y ^ (n - 1) ∉ Ideal.span {x ^ n, y ^ n})

/- In a Noetherian local ring, a length-2 regular sequence `x, y` in the maximal
ideal admits no coefficients `a, b` with `x ^ (n - 1) * y ^ (n - 1) = a * x ^ n + b * y ^ n`
for `n ≥ 2`. -/
#check (RingTheory.Sequence.IsRegular.not_exists_eq_mul_pow_add_mul_pow :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {x y : R}
      (hx : x ∈ maximalIdeal R) (hy : y ∈ maximalIdeal R)
      (hxy : IsRegular R [x, y]) {n : ℕ} (hn : 2 ≤ n),
      ¬ ∃ a b : R, x ^ (n - 1) * y ^ (n - 1) = a * x ^ n + b * y ^ n)
