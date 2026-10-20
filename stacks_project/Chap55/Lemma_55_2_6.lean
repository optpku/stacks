/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.LinearAlgebra.Matrix.ConnectedCoker
import StacksCheckRecall

@[expose] public section

open scoped BigOperators
open Matrix

/- Lemma 55.2.6 -/
@[stacks 0C6X] #check (Matrix.finrank_torsionBy_coker_le_cycleRank :
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (m : Fin n → ℤ),
    A.IsSymm →
    (∀ i j, i ≠ j → 0 ≤ A i j) →
    (∀ i, 0 < m i) →
    A *ᵥ m = 0 →
    (∀ I : Set (Fin n), I.Nonempty → I ≠ Set.univ →
      ∃ i ∈ I, ∃ j ∉ I, A i j ≠ 0) →
    (ℓ : ℕ) → [Fact ℓ.Prime] →
    (∀ i j, Nat.Coprime ℓ (A i j).natAbs) →
    (∀ i, Nat.Coprime ℓ (m i).natAbs) →
    Module.finrank (ZMod ℓ)
        (AddSubgroup.torsionBy
          ((Fin n → ℤ) ⧸ LinearMap.range (Matrix.toLin' A)) (ℓ : ℤ)) ≤
      (Finset.univ.filter fun ij : Fin n × Fin n ↦
        ij.1 < ij.2 ∧ 0 < A ij.1 ij.2).card + 1 - n)
