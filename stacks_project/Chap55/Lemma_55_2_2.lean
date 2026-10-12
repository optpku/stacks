/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.Matrix.WeightedKernel
import StacksCheckRecall

@[expose] public section

/- Lemma 55.2.2 (local erratum: symmetry added): the original nonsymmetric
assertion is false by a two-by-two counterexample; this symmetric version was
approved on 2026-10-01 and the uploaded source remains unchanged. -/
@[stacks 0C5V] #check (Matrix.ker_mulVecLin_eq_span_weightedIndicators :
    ∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {m : Fin n → ℝ},
      A.IsSymm →
      (∀ i j, i ≠ j → 0 ≤ A i j) →
      (∀ i, 0 < m i) →
      (∀ i, -A i i * m i ≥ ∑ j ∈ Finset.univ.erase i, A i j * m j) →
      A.mulVecLin.ker =
        Submodule.span ℝ {x : Fin n → ℝ |
          ∃ I : Set (Fin n),
            x = I.indicator m ∧
            (∀ i ∈ I, ∀ j ∉ I, A i j = 0) ∧
            ∀ i ∈ I,
              -A i i * m i = ∑ j ∈ Finset.univ.erase i, A i j * m j})
