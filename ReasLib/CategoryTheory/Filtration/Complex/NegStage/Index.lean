/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.NegStage

/-!
# Arithmetic API for negative filtration indices

The negative-stage construction uses one fixed embedding of `ℕ` into the
negative integers.  These small computation and order lemmas keep clients
from repeating coercion-heavy integer arithmetic at every tower boundary.
-/

@[expose] public section

noncomputable section

universe u

namespace CategoryTheory.FilteredComplex.NegStage

/-- The zeroth negative-stage index is zero. -/
@[simp, stacks 0D8Z]
theorem index_zero : index 0 = 0 := sorry

/-- Consecutive negative-stage indices differ by one. -/
@[simp, stacks 0D8Z]
theorem index_succ (n : ℕ) : index (n + 1) = index n - (1 : ℤ) := sorry

/-- Consecutive negative-stage indices occur in the order needed for a stage comparison. -/
@[stacks 0D8Z]
theorem index_succ_le (n : ℕ) : index (n + 1) ≤ index n := sorry

/-- The order on negative-stage indices is the reverse natural-number order. -/
@[stacks 0D8Z]
theorem index_le_iff {m n : ℕ} : index m ≤ index n ↔ n ≤ m := sorry

/-- Strict order on negative-stage indices is the reverse strict natural-number order. -/
@[stacks 0D8Z]
theorem index_lt_iff {m n : ℕ} : index m < index n ↔ n < m := sorry

/-- Addition of stages translates to subtraction of the corresponding integer index. -/
@[stacks 0D8Z]
theorem index_add (m n : ℕ) : index (m + n) = index m - (n : ℤ) := sorry

end CategoryTheory.FilteredComplex.NegStage
