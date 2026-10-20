/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.RingTheory.Subring.Powers

universe u

/- Lemma 29.46.4: Let `A` be a subring of a commutative ring `B`. If `b ∉ A`, while `b ^ n ∈ A`
and `b ^ (n + 1) ∈ A` for some `n ≥ 2`, then some `b' ∉ A` has both `b' ^ 2 ∈ A` and
`b' ^ 3 ∈ A`. -/
@[stacks 0CNA] #check
  (Subring.exists_not_mem_sq_cube_mem_of_pow_mem_of_pow_succ_mem :
    ∀ {B : Type u} [CommRing B] (A : Subring B) {b : B} {n : ℕ},
      2 ≤ n → b ∉ A → b ^ n ∈ A → b ^ (n + 1) ∈ A →
        ∃ b' : B, b' ∉ A ∧ b' ^ 2 ∈ A ∧ b' ^ 3 ∈ A)
