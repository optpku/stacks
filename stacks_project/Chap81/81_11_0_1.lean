/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap81.«81_11_0_1_Glueing»
import StacksCheckRecall

open AlgebraicGeometry.AlgebraicSpace.FormalGlueing

/- 81.11.0.1: the canonical functor Spaces/X ⟶ Spaces(Y → X, Z) sending
X' ⟶ X to U ×_X X' ← V ×_X X' → Y ×_X X', where Spaces(Y → X, Z) is the
category of commutative diagrams U' ← V' → Y' over U ← V → Y with both
squares cartesian. -/
@[stacks 0AF3] #check AlgebraicGeometry.AlgebraicSpace.FormalGlueing.functor
