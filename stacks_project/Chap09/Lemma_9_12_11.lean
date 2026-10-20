/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.SeparableDegree
import StacksCheckRecall

@[expose] public section

/- Lemma 9.12.11 [stacks 09HA]: the embedding-count formulation is the composite of the
algebraically closed target comparison with the canonical separable-degree finrank bounds. -/
@[stacks 09HA]
#check Field.finSepDegree_eq_of_isAlgClosed
#check Field.finSepDegree_le_finrank
#check Field.finSepDegree_eq_finrank_iff
