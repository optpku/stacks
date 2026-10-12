/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Symmetric

@[expose] public section

open scoped BigOperators

namespace Matrix

/-- For a symmetric real matrix with nonnegative off-diagonal entries and a
positive vector satisfying the weighted row inequalities, the kernel of the
associated linear map is spanned by weighted indicator vectors of subsets with
no outgoing entries and saturated row inequalities. -/
theorem ker_mulVecLin_eq_span_weightedIndicators
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {m : Fin n → ℝ}
    (h_symmetric : A.IsSymm)
    (h_offDiagonal : ∀ i j, i ≠ j → 0 ≤ A i j)
    (h_positive : ∀ i, 0 < m i)
    (h_dominant :
      ∀ i, -A i i * m i ≥ ∑ j ∈ Finset.univ.erase i, A i j * m j) :
    A.mulVecLin.ker =
      Submodule.span ℝ {x : Fin n → ℝ |
        ∃ I : Set (Fin n),
          x = I.indicator m ∧
          (∀ i ∈ I, ∀ j ∉ I, A i j = 0) ∧
          ∀ i ∈ I,
            -A i i * m i = ∑ j ∈ Finset.univ.erase i, A i j * m j} := sorry

end Matrix
