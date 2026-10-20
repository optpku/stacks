/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.ForkedSeven

/- Lemma 55.5.13: seven distinct `(-2)`-indices forming the specified forked chain
in a numerical type with more than seven indices have the displayed common weight,
intersection matrix, and multiplicity inequalities. -/
@[stacks 0C8J] #check (NumericalType.forkedSevenClassification :
  ∀ (T : NumericalType), 7 < T.n → ∀ (v : Fin 7 ↪ Fin T.n),
    (∀ r, NumericalType.IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r)) →
    T.intersection (v 0) (v 1) ≠ 0 →
    T.intersection (v 1) (v 2) ≠ 0 →
    T.intersection (v 2) (v 3) ≠ 0 →
    T.intersection (v 3) (v 4) ≠ 0 →
    T.intersection (v 4) (v 5) ≠ 0 →
    T.intersection (v 3) (v 6) ≠ 0 →
    NumericalType.IsForkedSevenConfiguration T v)
