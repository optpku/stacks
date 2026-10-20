/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.LinearThree

/- Lemma 55.5.2: in a numerical type with more than three indices, three distinct
`(-2)`-indices with at least two nonzero pairwise intersections have, up to
reordering, one of the three displayed weighted linear configurations. -/
@[stacks 0C7R] #check (NumericalType.linearThreeClassification :
  ∀ (T : NumericalType), 3 < T.n → (v : Fin 3 ↪ Fin T.n) →
    (∀ r,
      NumericalType.IsMinusTwoIndex T.componentGenus T.weight T.intersection
        (v r)) →
    ((T.intersection (v 0) (v 1) ≠ 0 ∧
        T.intersection (v 0) (v 2) ≠ 0) ∨
      (T.intersection (v 0) (v 1) ≠ 0 ∧
        T.intersection (v 1) (v 2) ≠ 0) ∨
      (T.intersection (v 0) (v 2) ≠ 0 ∧
        T.intersection (v 1) (v 2) ≠ 0)) →
    ∃ p : Equiv.Perm (Fin 3),
      NumericalType.IsLinearThreeConfiguration T (p.toEmbedding.trans v))
