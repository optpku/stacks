/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Definition_76_48_1_LocalCompleteIntersection
import StacksCheckRecall

@[expose] public section

/- Definition 76.48.1 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is a Koszul morphism, or a local complete intersection morphism, if the equivalent
conditions of Lemma 67.22.1 hold with `P` = local complete intersection. -/
@[stacks 06C4] #check AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection

/- Definition 76.48.1 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is Koszul at a point `x` of `|X|` if some open neighbourhood `X' ⊂ X` of `x` has
local-complete-intersection restriction `f|_{X'} : X' ⟶ Y`. -/
@[stacks 06C4] #check AlgebraicGeometry.AlgebraicSpace.KoszulAt
