module

public import stacks_project.Chap55.Lemma_55_2_2
public import ReasLib.LinearAlgebra.Matrix.NegativeSemidefinite
import StacksCheckRecall

@[expose] public section

open scoped BigOperators
open Matrix

/- Lemma 55.2.3 (1): a symmetric real matrix with nonnegative off-diagonal
entries, a positive kernel vector, and no proper nonempty subset disconnected
from its complement has nonpositive quadratic form. -/
@[stacks 0C5X] #check (Matrix.dotProduct_mulVec_nonpos_of_connected :
    ∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {m : Fin n → ℝ},
      A.IsSymm →
      (∀ i j, i ≠ j → 0 ≤ A i j) →
      (∀ i, 0 < m i) →
      A *ᵥ m = 0 →
      (∀ I : Set (Fin n), I.Nonempty → I ≠ Set.univ →
        ∃ i ∈ I, ∃ j ∉ I, A i j ≠ 0) →
      ∀ x : Fin n → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ 0)

/- Lemma 55.2.3 (2): under the same hypotheses, the quadratic form vanishes
exactly on the real multiples of the positive kernel vector. -/
@[stacks 0C5X] #check (Matrix.dotProduct_mulVec_eq_zero_iff_of_connected :
    ∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {m : Fin n → ℝ},
      A.IsSymm →
      (∀ i j, i ≠ j → 0 ≤ A i j) →
      (∀ i, 0 < m i) →
      A *ᵥ m = 0 →
      (∀ I : Set (Fin n), I.Nonempty → I ≠ Set.univ →
        ∃ i ∈ I, ∃ j ∉ I, A i j ≠ 0) →
      ∀ x : Fin n → ℝ,
        x ⬝ᵥ (A *ᵥ x) = 0 ↔ ∃ q : ℝ, x = q • m)
