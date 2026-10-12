/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Ring.Subring.Basic

@[expose] public section

namespace Subring

/-- If an element outside a subring has two consecutive powers of exponent at least two in the
subring, then some element outside the subring has both its square and cube in the subring. -/
theorem exists_not_mem_sq_cube_mem_of_pow_mem_of_pow_succ_mem {B : Type u} [CommRing B]
    (A : Subring B) {b : B} {n : ℕ} (hn : 2 ≤ n) (hb : b ∉ A) (hbn : b ^ n ∈ A)
    (hbn_succ : b ^ (n + 1) ∈ A) :
    ∃ b' : B, b' ∉ A ∧ b' ^ 2 ∈ A ∧ b' ^ 3 ∈ A := sorry

end Subring
