/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_7_5_SmoothLocal
import StacksCheckRecall

@[expose] public section

/- Definition 100.7.5: let `P` be a property of germs of schemes which is
smooth local. Let `X` be an algebraic stack. Let `x ∈ |X|`. We say `X` has
property `P` at `x` if any of the equivalent conditions of Lemma 100.7.4
holds. -/
@[stacks 04YJ] #check AlgebraicGeometry.AlgebraicStack.hasSmoothLocalAt
