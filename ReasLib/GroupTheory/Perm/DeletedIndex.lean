/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.CrossRefAttribute

/-! @stack 01FH -/

@[expose] public section

namespace Equiv.Perm

/-- Delete the source index `j` from a permutation of `Fin (n + 1)`.

The result acts on the complementary `Fin n` after the deleted source and target positions have
both been moved to the distinguished zero position. This auxiliary permutation is used for
compatibility of the alternating Čech differential in Stacks 01FH. -/
@[stacks 01FH "permutation after deleting one index"]
abbrev deleteAt {n : ℕ} (τ : Equiv.Perm (Fin (n + 1))) (j : Fin (n + 1)) :
    Equiv.Perm (Fin n) :=
  (Equiv.Perm.decomposeFin ((τ j).cycleRange * τ * j.cycleRange.symm)).2

/-- The complementary permutation commutes with reinsertion by `succAbove`. -/
@[stacks 01FH "deleted permutation and succAbove"]
theorem deleteAt_comp_succAbove {n : ℕ} (τ : Equiv.Perm (Fin (n + 1)))
    (j : Fin (n + 1)) :
    τ ∘ j.succAboveEmb = (τ j).succAboveEmb ∘ deleteAt τ j := sorry

/-- The deleted permutation carries the alternating sign correction. -/
@[stacks 01FH "deleted permutation sign coefficient"]
theorem deleteAt_sign {n : ℕ} (τ : Equiv.Perm (Fin (n + 1))) (j : Fin (n + 1)) :
    ((-1 : ℤ) ^ (j : ℕ)) * Equiv.Perm.sign (deleteAt τ j) =
      Equiv.Perm.sign τ * ((-1 : ℤ) ^ (τ j : ℕ)) := sorry

end Equiv.Perm

end
