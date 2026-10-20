/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.MinusOneIndex

/- Lemma 55.3.7: if one contribution to the genus of a numerical type with more
than one index is negative, then that index has component genus zero and diagonal
intersection equal to the negative of its weight. -/
@[stacks 0C75] #check (NumericalType.isMinusOneIndex_of_contribution_neg :
    ∀ (T : NumericalType) (hn : 1 < T.n) (i : Fin T.n),
      (T.multiplicity i : ℚ) *
          ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
            (T.intersection i i : ℚ) / 2) < 0 →
        NumericalType.IsMinusOneIndex T.componentGenus T.weight T.intersection i)
