/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.LinearFour

/- Lemma 55.5.3: in a numerical type with more than four indices, four distinct
`(-2)`-indices joined successively have, up to reordering, one of the four
displayed weighted linear configurations. -/
@[stacks 0C7V] #check (NumericalType.linearFourClassification :
  (T : NumericalType) → 4 < T.n →
    (v : Fin 4 ↪ Fin T.n) →
    (∀ r, NumericalType.IsMinusTwoIndex T.componentGenus T.weight
      T.intersection (v r)) →
    (∀ r : Fin 3,
      T.intersection (v r.castSucc) (v r.succ) ≠ 0) →
    ∃ p : Equiv.Perm (Fin 4),
      NumericalType.IsLinearFourConfiguration T (p.toEmbedding.trans v))
