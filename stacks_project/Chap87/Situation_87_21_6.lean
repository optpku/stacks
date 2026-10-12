/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Situation_87_21_6_Completed
public import stacks_project.Chap87.Situation_87_21_6_BaseChange
import StacksCheckRecall

@[expose] public section

open TopologicalRing

/- Situation 87.21.6: a local property P of morphisms of WAdm^count is stable
under base change when P(B → A) implies P(C → A ⊗̂_B C). This is well-defined
because A ⊗̂_B C remains in WAdm^count by Lemma 87.4.12. -/
@[stacks 0GBC] #check TopologicalRing.IsLocalMorphismProperty.IsStableUnderBaseChange
