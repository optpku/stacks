/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_16_2_SmoothLocal
import StacksCheckRecall

@[expose] public section

/- Definition 101.16.2: let `P` be a property of morphisms of algebraic spaces
which is smooth local on the source-and-target. We say a morphism `f : X ⟶ Y`
of algebraic stacks has property `P` if the equivalent conditions of Lemma
101.16.1 hold. -/
@[stacks 06FN] #check AlgebraicGeometry.AlgebraicStack.hasSmoothLocalAtSourceAndTarget
