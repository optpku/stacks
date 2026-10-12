/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_28_1_Gerbe
import StacksCheckRecall

@[expose] public section

/- Definition 101.28.1 (1): a morphism `f : X ⟶ Y` of algebraic stacks makes
`X` a gerbe over `Y` when `f` is a gerbe morphism of stacks in groupoids over
`(Sch/S)_fppf`. -/
@[stacks 06QC] #check AlgebraicGeometry.AlgebraicStack.Gerbe

/- Definition 101.28.1 (2): an algebraic stack `X` is a gerbe if there exists a
morphism `X ⟶ A.toGroupoids` to an algebraic space which turns `X` into a
gerbe over that space. -/
@[stacks 06QC] #check AlgebraicGeometry.AlgebraicStack.IsGerbe
