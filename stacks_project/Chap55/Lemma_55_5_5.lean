/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.LinearFive

@[expose] public section

/- Lemma 55.5.5: in a numerical type with more than five indices, five distinct
`(-2)`-indices joined successively have, up to reordering, one of the three
displayed weighted linear configurations. -/
@[stacks 0C82] #check (NumericalType.linearFiveClassification :
  ∀ (T : NumericalType) (hn : 5 < T.n) (v : Fin 5 ↪ Fin T.n)
    (hminusTwo : ∀ r,
      NumericalType.IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r))
    (hchain : ∀ r : Fin 4,
      T.intersection (v r.castSucc) (v r.succ) ≠ 0),
    ∃ p : Equiv.Perm (Fin 5),
      NumericalType.IsLinearFiveConfiguration T (p.toEmbedding.trans v))
