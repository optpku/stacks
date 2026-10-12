/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.Graph

/- Lemma 55.5.6: in a numerical type with more than five indices, five distinct
`(-2)`-indices `v 0 = h`, `v 1 = i`, `v 2 = j`, `v 3 = k`, and `v 4 = l` cannot
have all four intersections from `h` to `i`, `j`, `k`, and `l` positive. -/
@[stacks 0C86] #check (NumericalType.noFourMinusTwoNeighbors :
  ∀ (T : NumericalType), 5 < T.n →
    ∀ (v : Fin 5 ↪ Fin T.n),
      (∀ r, NumericalType.IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r)) →
      0 < T.intersection (v 0) (v 1) →
      0 < T.intersection (v 0) (v 2) →
      0 < T.intersection (v 0) (v 3) →
      0 < T.intersection (v 0) (v 4) → False)
