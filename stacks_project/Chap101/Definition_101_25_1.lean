/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_25_5_Flat
import StacksCheckRecall

@[expose] public section

/- Definition 101.25.1: a morphism `f : X ⟶ Y` of algebraic stacks is
flat if the equivalent conditions of Lemma 101.16.1 hold with `P` = flat. -/
@[stacks 06PW] #check AlgebraicGeometry.AlgebraicStack.Flat
