/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_4_2_Comparison
import StacksCheckRecall

@[expose] public section

/- Lemma 66.4.2: let `S` be a scheme and let `X` be a scheme over `S`. The points of `X`
as a scheme are in canonical 1-1 correspondence with the points of `X` as an algebraic
space. -/
@[stacks 03BV] #check AlgebraicGeometry.AlgebraicSpace.ofOver.pointsEquiv
