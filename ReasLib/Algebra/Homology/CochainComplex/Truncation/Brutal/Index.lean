/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal
public import ReasLib.CategoryTheory.Filtration.Complex.NegStage.Index

/-!
# Arithmetic API for the brutal tower index

The brutal tower reuses the neutral negative-stage index.  These facade
lemmas keep arithmetic in the `Brutal.Tower` namespace while retaining one
canonical owner for the underlying integer sequence.
-/

@[expose] public section

noncomputable section

universe u

namespace CategoryTheory.CochainComplex.Brutal.Tower

/-- The brutal tower index is antitone. -/
@[stacks 0D8Z]
theorem index_anti : Antitone index := sorry

/-- The zeroth brutal tower index is zero. -/
@[simp, stacks 0D8Z]
theorem index_zero : index 0 = 0 := sorry

/-- Consecutive brutal tower indices differ by one. -/
@[simp, stacks 0D8Z]
theorem index_succ (n : ℕ) : index (n + 1) = index n - (1 : ℤ) := sorry

/-- Consecutive brutal tower indices occur in decreasing order. -/
@[stacks 0D8Z]
theorem index_succ_le (n : ℕ) : index (n + 1) ≤ index n := sorry

/-- The order on brutal tower indices is reverse natural-number order. -/
@[stacks 0D8Z]
theorem index_le_iff {m n : ℕ} : index m ≤ index n ↔ n ≤ m := sorry

/-- Strict order on brutal tower indices is reverse natural-number order. -/
@[stacks 0D8Z]
theorem index_lt_iff {m n : ℕ} : index m < index n ↔ n < m := sorry

/-- Addition of tower stages translates to subtraction of integer indices. -/
@[stacks 0D8Z]
theorem index_add (m n : ℕ) : index (m + n) = index m - (n : ℤ) := sorry

end CategoryTheory.CochainComplex.Brutal.Tower
