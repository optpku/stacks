/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.MinusTwoIndex

/- Lemma 55.3.15: if a contribution to the genus of a numerical type with more
than one index is zero, then that index has component genus zero and diagonal
intersection equal to `-2` times its weight. -/
@[stacks 0C7D] #check (NumericalType.isMinusTwoIndex_of_contribution_eq_zero :
    ∀ (T : NumericalType), 1 < T.n → (i : Fin T.n) →
      ((T.multiplicity i : ℚ) *
          ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
            (T.intersection i i : ℚ) / 2) = 0) →
      NumericalType.IsMinusTwoIndex T.componentGenus T.weight T.intersection i)
