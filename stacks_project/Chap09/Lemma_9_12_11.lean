/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
