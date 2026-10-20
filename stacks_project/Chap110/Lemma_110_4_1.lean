/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.TopCat.Limits.Noncompact
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

/- Lemma 110.4.1 -/
@[stacks 09ZK] #check
  (TopCat.Counterexample.NatQuasiCompact.exists_compactSpace_limit_not_compactSpace :
    ∃ F : ℕᵒᵖ ⥤ TopCat.{0},
      (∀ n, CompactSpace (F.obj n)) ∧ ¬ CompactSpace (limit F : TopCat))
