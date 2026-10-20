/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.ForkedFive

/- Lemma 55.5.7 -/
@[stacks 0C87] #check (NumericalType.forkedFiveClassification :
  (T : NumericalType) →
    5 < T.n →
    (v : Fin 5 ↪ Fin T.n) →
    (∀ r, NumericalType.IsMinusTwoIndex T.componentGenus T.weight T.intersection
      (v r)) →
    T.intersection (v 0) (v 1) ≠ 0 →
    T.intersection (v 1) (v 2) ≠ 0 →
    T.intersection (v 2) (v 3) ≠ 0 →
    T.intersection (v 2) (v 4) ≠ 0 →
    ∃ p : Equiv.Perm (Fin 5),
      NumericalType.IsForkedFiveConfiguration T (p.toEmbedding.trans v))
