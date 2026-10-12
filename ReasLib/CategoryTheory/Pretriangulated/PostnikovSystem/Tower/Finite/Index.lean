/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Reversed Indices of Finite Postnikov Towers

Positions in a finite Postnikov row are ordered oppositely to tower stages.  This leaf exposes
that reindexing through `Fin.rev` and owns the normalization API used by all finite restriction
constructions.
-/

@[expose] public section

namespace CategoryTheory.PostnikovSystem.Tower.Finite

/-- The tower stage represented by a position in a reversed finite row. -/
@[stacks 0D8Z "reversed finite-row index of a Postnikov tower"]
def index {n : ℕ} (i : Fin n) : ℕ :=
  i.rev.1

/-- The first position of a reversed row represents its largest tower index. -/
@[simp, stacks 0D8Z]
theorem index_zero (n : ℕ) :
    index (0 : Fin (n + 1)) = n := sorry

/-- The last position of a reversed row represents tower index zero. -/
@[simp, stacks 0D8Z]
theorem index_last (n : ℕ) :
    index (Fin.last n) = 0 := sorry

/-- Viewing a position in the larger type moves its reversed index up by one. -/
@[simp, stacks 0D8Z]
theorem index_castSucc {n : ℕ} (i : Fin n) :
    index i.castSucc = index i + 1 := sorry

/-- Moving a position one place to the right preserves its represented tower stage. -/
@[simp, stacks 0D8Z]
theorem index_succ {n : ℕ} (i : Fin n) :
    index i.succ = index i := sorry

end CategoryTheory.PostnikovSystem.Tower.Finite
