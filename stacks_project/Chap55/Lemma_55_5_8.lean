/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType.LinearChain
import StacksCheckRecall

@[expose] public section

/- Lemma 55.5.8 -/
@[stacks 0C89] #check
  (NumericalType.linearChainClassification :
    (T : NumericalType) → (t : ℕ) → 5 < t → t < T.n →
      (v : Fin t ↪ Fin T.n) →
      (∀ r, NumericalType.IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r)) →
      (∀ r s, r.val + 1 = s.val → T.intersection (v r) (v s) ≠ 0) →
      NumericalType.IsLinearChainConfiguration T v ∨
        NumericalType.IsLinearChainConfiguration T
          ((Fin.revPerm : Equiv.Perm (Fin t)).toEmbedding.trans v))
