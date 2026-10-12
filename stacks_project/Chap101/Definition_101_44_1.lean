/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_44_4_LocalCompleteIntersection
import StacksCheckRecall

@[expose] public section

/- Definition 101.44.1: a morphism `f : X ⟶ Y` of algebraic stacks is
a local complete intersection morphism, or Koszul, if the equivalent
conditions of Lemma 101.16.1 hold with `P` = local complete intersection. -/
@[stacks 0CJ3] #check AlgebraicGeometry.AlgebraicStack.IsLocalCompleteIntersection
