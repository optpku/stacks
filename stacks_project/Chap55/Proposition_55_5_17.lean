/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.ProperSubgraphClassification

@[expose] public section

/- Proposition 55.5.17: a proper finite subset of at least two `(-2)`-indices
with no zero-intersection cut has, after reordering, one of the configurations
classified in Lemmas 55.5.1, 55.5.2, 55.5.3, 55.5.4, 55.5.5, 55.5.7, 55.5.8,
55.5.9, 55.5.10, 55.5.13, or 55.5.14. -/
@[stacks 0C8Q] #check (NumericalType.minusTwoSubsetClassification :
  (T : NumericalType) →
    (I : Finset (Fin T.n)) →
    2 ≤ I.card →
    I ≠ Finset.univ →
    (∀ i ∈ I,
      NumericalType.IsMinusTwoIndex T.componentGenus T.weight T.intersection i) →
    (¬ ∃ J : Finset (Fin T.n),
      J.Nonempty ∧ J ⊆ I ∧ J ≠ I ∧
        ∀ i' ∈ J, ∀ i ∈ I \ J, T.intersection i' i = 0) →
    ((∃ v₂ : Fin 2 ↪ Fin T.n,
        Finset.univ.map v₂ = I ∧ NumericalType.IsLinearTwoConfiguration T v₂) ∨
      (∃ v₃ : Fin 3 ↪ Fin T.n,
        Finset.univ.map v₃ = I ∧ NumericalType.IsLinearThreeConfiguration T v₃) ∨
      (∃ v₄ : Fin 4 ↪ Fin T.n,
        Finset.univ.map v₄ = I ∧
          (NumericalType.IsLinearFourConfiguration T v₄ ∨
            NumericalType.IsForkedFourConfiguration T v₄)) ∨
      (∃ v₅ : Fin 5 ↪ Fin T.n,
        Finset.univ.map v₅ = I ∧
          (NumericalType.IsLinearFiveConfiguration T v₅ ∨
            NumericalType.IsForkedFiveConfiguration T v₅)) ∨
      (∃ t : ℕ, 5 < t ∧ ∃ v : Fin t ↪ Fin T.n,
        Finset.univ.map v = I ∧ NumericalType.IsLinearChainConfiguration T v) ∨
      (∃ t : ℕ, 4 < t ∧ ∃ v : Fin (t + 1) ↪ Fin T.n,
        Finset.univ.map v = I ∧ NumericalType.IsForkedChainConfiguration T v) ∨
      (∃ v₆ : Fin 6 ↪ Fin T.n,
        Finset.univ.map v₆ = I ∧ NumericalType.IsForkedSixConfiguration T v₆) ∨
      (∃ v₇ : Fin 7 ↪ Fin T.n,
        Finset.univ.map v₇ = I ∧ NumericalType.IsForkedSevenConfiguration T v₇) ∨
      (∃ v₈ : Fin 8 ↪ Fin T.n,
        Finset.univ.map v₈ = I ∧ NumericalType.IsForkedEightConfiguration T v₈)))
