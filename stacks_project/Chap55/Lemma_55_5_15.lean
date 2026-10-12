/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.Graph

@[expose] public section

namespace NumericalType

/- Lemma 55.5.15: in a numerical type with more than eight indices, eight distinct
`(-2)`-indices `v 0 = e`, `v 1 = f`, `v 2 = g`, `v 3 = h`, `v 4 = i`, `v 5 = j`,
`v 6 = k`, and `v 7 = l` cannot have all seven indicated intersections nonzero. -/
@[stacks 0C8N] #check (NumericalType.noForkedSevenChainMinusTwoSubgraph :
  ∀ (T : NumericalType), 8 < T.n →
    (v : Fin 8 ↪ Fin T.n) →
    (∀ r, IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r)) →
    T.intersection (v 0) (v 1) ≠ 0 →
    T.intersection (v 1) (v 2) ≠ 0 →
    T.intersection (v 2) (v 3) ≠ 0 →
    T.intersection (v 3) (v 4) ≠ 0 →
    T.intersection (v 4) (v 5) ≠ 0 →
    T.intersection (v 5) (v 6) ≠ 0 →
    T.intersection (v 7) (v 3) ≠ 0 → False)

end NumericalType
