/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic

open scoped BigOperators

@[expose] public section

universe u

namespace Matrix

/-- Weighted off-diagonal row inequalities are equivalent to pointwise nonpositivity
of the corresponding matrix-vector product. -/
theorem neg_diag_dominates_iff_mulVec_nonpos {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (m : ι → ℝ) :
    (∀ i, -A i i * m i ≥ ∑ j ∈ Finset.univ.erase i, A i j * m j) ↔
      A *ᵥ m ≤ 0 := sorry

/-- Equality in a weighted off-diagonal row inequality is equivalent to vanishing of the
corresponding coordinate of the matrix-vector product. -/
lemma neg_diag_eq_sum_erase_iff_mulVec_eq_zero {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (m : ι → ℝ) (i : ι) :
    (-A i i * m i = ∑ j ∈ Finset.univ.erase i, A i j * m j) ↔
      (A *ᵥ m) i = 0 := sorry

end Matrix
