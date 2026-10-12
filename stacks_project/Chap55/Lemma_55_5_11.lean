/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.NumericalType.Graph

@[expose] public section

/- Lemma 55.5.11: if `4 ≤ t` and a numerical type has more than `t + 2` indices,
then `t + 2` distinct `(-2)`-indices cannot have positive intersections along
the chain from indices `1` through `t`, together with the edges `0`–`2` and
`(t - 1)`–`(t + 1)`. -/
@[stacks 0C8H] #check (NumericalType.noDoubleForkMinusTwoSubgraph :
    ∀ (T : NumericalType) (t : ℕ), 4 ≤ t → t + 2 < T.n →
      ∀ (v : Fin (t + 2) ↪ Fin T.n),
      (∀ r, NumericalType.IsMinusTwoIndex T.componentGenus T.weight T.intersection
        (v r)) →
      (∀ r s, 1 ≤ r.val → r.val + 1 = s.val → s.val ≤ t →
        0 < T.intersection (v r) (v s)) →
      (∀ r s, r.val = 0 → s.val = 2 →
        0 < T.intersection (v r) (v s)) →
      (∀ r s, r.val + 1 = t → s.val = t + 1 →
        0 < T.intersection (v r) (v s)) → False)
