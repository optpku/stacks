/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_36_4_Unramified
import StacksCheckRecall

@[expose] public section

/- Definition 101.36.1: a morphism `f : X ⟶ Y` of algebraic stacks is
unramified if it is DM and the equivalent conditions of Lemma 101.34.1
hold with `P` = unramified. -/
@[stacks 0CIT] #check AlgebraicGeometry.AlgebraicStack.Unramified
