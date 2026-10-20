/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Gershgorin

@[expose] public section

open scoped BigOperators

namespace Matrix

/-- A complex square matrix whose columns can be positively weighted to satisfy
strict row diagonal dominance has nonzero determinant. -/
theorem det_ne_zero_of_exists_weighted_row_dominance
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (h : ∃ m : Fin n → ℝ, (∀ i, 0 < m i) ∧
      ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j * (m j : ℂ)‖ < ‖A i i * (m i : ℂ)‖) :
    Matrix.det A ≠ 0 := sorry

end Matrix
