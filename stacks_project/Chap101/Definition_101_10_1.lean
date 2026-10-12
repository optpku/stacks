/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_10_1_Integral
import StacksCheckRecall

@[expose] public section

/- Definition 101.10.1 (1): a morphism `f : X ⟶ Y` of algebraic stacks is
integral if it is representable and integral in the sense of Properties of
Stacks, Section 100.3. -/
@[stacks 0CHU] #check AlgebraicGeometry.AlgebraicStack.IsIntegralHom

/- Definition 101.10.1 (2): a morphism `f : X ⟶ Y` of algebraic stacks is
finite if it is representable and finite in the sense of Properties of
Stacks, Section 100.3. -/
@[stacks 0CHU] #check AlgebraicGeometry.AlgebraicStack.IsFinite
