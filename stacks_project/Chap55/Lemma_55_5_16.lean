/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.Graph

@[expose] public section

namespace NumericalType

/- Lemma 55.5.16: in a numerical type with more than nine indices, nine distinct
`(-2)`-indices `v 0 = d`, `v 1 = e`, `v 2 = f`, `v 3 = g`, `v 4 = h`, `v 5 = i`,
`v 6 = j`, `v 7 = k`, and `v 8 = l` cannot have all eight indicated intersections
nonzero. -/
@[stacks 0C8P] #check (NumericalType.noForkedEightChainMinusTwoSubgraph :
  ∀ (T : NumericalType), 9 < T.n →
    (v : Fin 9 ↪ Fin T.n) →
    (∀ r, IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r)) →
    T.intersection (v 0) (v 1) ≠ 0 →
    T.intersection (v 1) (v 2) ≠ 0 →
    T.intersection (v 2) (v 3) ≠ 0 →
    T.intersection (v 3) (v 4) ≠ 0 →
    T.intersection (v 4) (v 5) ≠ 0 →
    T.intersection (v 5) (v 6) ≠ 0 →
    T.intersection (v 6) (v 7) ≠ 0 →
    T.intersection (v 8) (v 4) ≠ 0 → False)

end NumericalType
