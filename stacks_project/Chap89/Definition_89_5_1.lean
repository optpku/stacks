/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap89.Definition_89_5_1_NormalizedBlowup
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- Definition 89.5.1: Let `S` be a scheme. Let `X` be a decent algebraic space over `S`
satisfying the equivalent conditions of Morphisms of Spaces, Lemma 67.49.1. Let `x ∈ |X|`
be a closed point. The normalized blowup of `X` at `x` is the composition `X'' ⟶ X' ⟶ X`
where `X' ⟶ X` is the blowup of `X` at `x` (Definition 89.4.1) and `X'' ⟶ X'` is the
normalization of `X'`. -/
@[stacks 0BHJ] #check AlgebraicGeometry.AlgebraicSpace.NormalizedBlowup
#check AlgebraicGeometry.AlgebraicSpace.NormalizedBlowup.of
#check AlgebraicGeometry.AlgebraicSpace.NormalizedBlowup.hom
#check AlgebraicGeometry.AlgebraicSpace.NormalizedBlowup.source
#check AlgebraicGeometry.AlgebraicSpace.NormalizedBlowup.spec
