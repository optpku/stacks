/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.IntermediateField.SeparableTower
import StacksCheckRecall

@[expose] public section

/- Lemma 9.12.10 (Tag 09H9): a finite generator tower is separable when each generator is
separable over its preceding stage; this gives the embedding-count equality over an algebraically
closed target and the strict inequality when a successive generator is inseparable. The source
stage is `FieldExtension.adjoinStage F α i`. -/
#check FieldExtension.adjoinStage_isSeparable
#check FieldExtension.adjoinTower_isSeparable
@[stacks 09H9]
#check FieldExtension.adjoinTower_card_algHom_eq_finrank
#check FieldExtension.adjoinTower_card_algHom_lt_finrank
