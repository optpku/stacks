/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_23_2_GeometricallyUnibranch
public import stacks_project.Chap67.Lemma_67_30_5_Flat

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricallyUnibranchAt

/-- Lemma 74.9.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `x` be a point of `|X|`. If `f` is flat at `x` and `X` is
geometrically unibranch at `x`, then `Y` is geometrically unibranch at
`Points.map f x`. -/
@[stacks 06DQ]
theorem of_flatAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X)
    (hf : FlatAt f x) [GeometricallyUnibranchAt X x] :
    GeometricallyUnibranchAt Y (Points.map f x) := sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricallyUnibranchAt
