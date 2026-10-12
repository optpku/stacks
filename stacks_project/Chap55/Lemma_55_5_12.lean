/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.Graph

@[expose] public section

/- Lemma 55.5.12: in a numerical type with more than seven indices, seven distinct
`(-2)`-indices `v 0 = f`, `v 1 = g`, `v 2 = h`, `v 3 = i`, `v 4 = j`, `v 5 = k`,
and `v 6 = l` cannot have all six indicated branch intersections nonzero. -/
@[stacks 0C8I] #check (NumericalType.noThreeArmedMinusTwoSubgraph :
  ∀ (T : NumericalType), 7 < T.n → ∀ (v : Fin 7 ↪ Fin T.n),
    (∀ r, NumericalType.IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r)) →
    T.intersection (v 0) (v 1) ≠ 0 → T.intersection (v 1) (v 2) ≠ 0 →
    T.intersection (v 3) (v 4) ≠ 0 → T.intersection (v 4) (v 2) ≠ 0 →
    T.intersection (v 5) (v 6) ≠ 0 → T.intersection (v 6) (v 2) ≠ 0 → False)
