/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.Matrix.WeightedKernel
public import ReasLib.LinearAlgebra.Matrix.MulVecOrder

@[expose] public section

open scoped BigOperators

namespace Matrix

/-- A symmetric real matrix with nonnegative off-diagonal entries, a positive
kernel vector, and no proper nonempty subset disconnected from its complement
has a nonpositive quadratic form. -/
theorem dotProduct_mulVec_nonpos_of_connected
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {m : Fin n → ℝ}
    (h_symmetric : A.IsSymm)
    (h_offDiagonal : ∀ i j, i ≠ j → 0 ≤ A i j)
    (h_positive : ∀ i, 0 < m i)
    (h_kernel : A *ᵥ m = 0)
    (h_connected : ∀ I : Set (Fin n), I.Nonempty → I ≠ Set.univ →
      ∃ i ∈ I, ∃ j ∉ I, A i j ≠ 0) :
    ∀ x : Fin n → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ 0 := sorry

/-- The quadratic form of a symmetric real matrix with nonnegative off-diagonal
entries, a positive kernel vector, and no proper nonempty subset disconnected
from its complement vanishes exactly on real multiples of that kernel vector. -/
theorem dotProduct_mulVec_eq_zero_iff_of_connected
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {m : Fin n → ℝ}
    (h_symmetric : A.IsSymm)
    (h_offDiagonal : ∀ i j, i ≠ j → 0 ≤ A i j)
    (h_positive : ∀ i, 0 < m i)
    (h_kernel : A *ᵥ m = 0)
    (h_connected : ∀ I : Set (Fin n), I.Nonempty → I ≠ Set.univ →
      ∃ i ∈ I, ∃ j ∉ I, A i j ≠ 0) :
    ∀ x : Fin n → ℝ,
      x ⬝ᵥ (A *ᵥ x) = 0 ↔ ∃ q : ℝ, x = q • m := sorry

end Matrix
