/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.ForkedEight

/- Lemma 55.5.14: eight distinct `(-2)`-indices in the specified forked
   configuration in a numerical type with more than eight indices have the displayed
   common weight, intersection matrix, and multiplicity inequalities. -/
@[stacks 0C8L] #check (NumericalType.forkedEightClassification :
  ∀ (T : NumericalType), 8 < T.n → ∀ (v : Fin 8 ↪ Fin T.n),
    (∀ r, NumericalType.IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r)) →
    T.intersection (v 0) (v 1) ≠ 0 →
    T.intersection (v 1) (v 2) ≠ 0 →
    T.intersection (v 2) (v 3) ≠ 0 →
    T.intersection (v 3) (v 4) ≠ 0 →
    T.intersection (v 4) (v 5) ≠ 0 →
    T.intersection (v 5) (v 6) ≠ 0 →
    T.intersection (v 4) (v 7) ≠ 0 →
    NumericalType.IsForkedEightConfiguration T v)
