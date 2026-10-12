/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_8_1_Noetherian
import StacksCheckRecall

@[expose] public section

/- Definition 101.8.1: an algebraic stack `X` is Noetherian if it is
quasi-compact, quasi-separated and locally Noetherian. -/
@[stacks 0510] #check AlgebraicGeometry.AlgebraicStack.IsNoetherian
