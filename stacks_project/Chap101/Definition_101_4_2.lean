/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_4_2_Separation
public import stacks_project.Chap101.Definition_101_8_1_Noetherian
import StacksCheckRecall

@[expose] public section

/- Definition 101.4.2 (1): an algebraic stack over S is DM over S if the
structure morphism is DM. -/
@[stacks 050D] #check AlgebraicGeometry.AlgebraicStack.IsDMOver

/- Definition 101.4.2 (2): an algebraic stack over S is quasi-DM over S if the
structure morphism is quasi-DM. -/
@[stacks 050D] #check AlgebraicGeometry.AlgebraicStack.IsQuasiDMOver

/- Definition 101.4.2 (3): an algebraic stack over S is separated over S if the
structure morphism is separated. -/
@[stacks 050D] #check AlgebraicGeometry.AlgebraicStack.IsSeparatedOver

/- Definition 101.4.2 (4): an algebraic stack over S is quasi-separated over S
if the structure morphism is quasi-separated. -/
@[stacks 050D] #check AlgebraicGeometry.AlgebraicStack.IsQuasiSeparatedOver

/- Definition 101.4.2 (5): an algebraic stack is DM if it is DM over Spec ℤ
after viewing via Algebraic Stacks, Definition 94.19.2. -/
@[stacks 050D] #check AlgebraicGeometry.AlgebraicStack.IsDM

/- Definition 101.4.2 (6): an algebraic stack is quasi-DM if it is quasi-DM
over Spec ℤ after viewing via Algebraic Stacks, Definition 94.19.2. -/
@[stacks 050D] #check AlgebraicGeometry.AlgebraicStack.IsQuasiDM

/- Definition 101.4.2 (7): an algebraic stack is separated if it is separated
over Spec ℤ after viewing via Algebraic Stacks, Definition 94.19.2. -/
@[stacks 050D] #check AlgebraicGeometry.AlgebraicStack.IsSeparated

/- Definition 101.4.2 (8): an algebraic stack is quasi-separated if it is
quasi-separated over Spec ℤ after viewing via Algebraic Stacks,
Definition 94.19.2. -/
@[stacks 050D] #check AlgebraicGeometry.AlgebraicStack.IsQuasiSeparated
