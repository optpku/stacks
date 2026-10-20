module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
import ReasLib.LinearAlgebra.Matrix.DiagonalDominance
import StacksCheckRecall

@[expose] public section

open scoped BigOperators

/- Lemma 55.2.1 (2): if a complex square matrix is strictly row diagonally dominant
after weighting its columns by positive real numbers, then its determinant is nonzero. -/
@[stacks 0C5U] #check
  (Matrix.det_ne_zero_of_exists_weighted_row_dominance :
    ∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ},
      (∃ m : Fin n → ℝ, (∀ i, 0 < m i) ∧
        ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j * (m j : ℂ)‖ <
          ‖A i i * (m i : ℂ)‖) → Matrix.det A ≠ 0)

/- Unweighted companion for Lemma 55.2.1 (1): a complex square matrix with strict row diagonal dominance
has nonzero determinant. -/
#check
  (det_ne_zero_of_sum_row_lt_diag :
    ∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ},
      (∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ < ‖A i i‖) → Matrix.det A ≠ 0)
