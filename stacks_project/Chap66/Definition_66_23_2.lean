/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_23_2_GeometricallyUnibranch
import StacksCheckRecall

@[expose] public section

/- Definition 66.23.2 (1): for a scheme `S`, an algebraic space `X` over `S`, and a point
`x ∈ |X|`, we say `X` is geometrically unibranch at `x` if the equivalent conditions of
Lemma 66.23.1 hold. -/
@[stacks 06DL] #check AlgebraicGeometry.AlgebraicSpace.GeometricallyUnibranchAt

/- Definition 66.23.2 (2): we say that `X` is geometrically unibranch if `X` is
geometrically unibranch at every `x ∈ |X|`. -/
@[stacks 06DL] #check AlgebraicGeometry.AlgebraicSpace.IsGeometricallyUnibranch
