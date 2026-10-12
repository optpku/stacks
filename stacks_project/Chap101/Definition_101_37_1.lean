/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_37_1_FiniteType
public import stacks_project.Chap101.Definition_101_37_1_Proper
import StacksCheckRecall

@[expose] public section

/- Definition 101.37.1: a morphism `f : X ⟶ Y` of algebraic stacks is
proper if it is separated, finite type, and universally closed. -/
@[stacks 0CL5] #check AlgebraicGeometry.AlgebraicStack.Proper
