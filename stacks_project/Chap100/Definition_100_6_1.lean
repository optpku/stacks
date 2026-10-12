/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_6_1_QuasiCompact
import StacksCheckRecall

@[expose] public section

/- Definition 100.6.1: an algebraic stack `X` is quasi-compact if and only if
the topological space `|X|` is quasi-compact. The Lean owner is the equivalent
existence of a surjective smooth atlas from a quasi-compact scheme. -/
@[stacks 04YB] #check AlgebraicGeometry.AlgebraicStack.IsQuasiCompact
