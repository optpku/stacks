/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Situation_87_21_2_MorphismProperty
import StacksCheckRecall

@[expose] public section

open TopologicalRing

/- Situation 87.21.2: a property P of morphisms of WAdm^count is local when it
is stable under étale weak-ideal completion squares, descends along those
squares when A → A' is faithfully flat, and is stable under finite products of
targets. -/
@[stacks 0CBA] #check TopologicalRing.IsLocalMorphismProperty
