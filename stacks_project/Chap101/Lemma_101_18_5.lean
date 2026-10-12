/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_18_4_FiniteTypePoint
public import stacks_project.Chap100.Definition_100_5_1_Surjective

/-!
# Images of finite type points under surjective locally finite type morphisms

A surjective locally-of-finite-type morphism of algebraic stacks sends finite-type
points onto finite-type points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType

/-- Lemma 101.18.5: Let `f : X ⟶ Y` be a morphism of algebraic stacks. If `f`
is locally of finite type and surjective, then
`Points.map f '' finiteTypePoints X = finiteTypePoints Y`. -/
@[stacks 06G1]
theorem image_finiteTypePoints_eq_of_surjective {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [LocallyOfFiniteType f] [Surjective f] :
    Points.map f '' finiteTypePoints X = finiteTypePoints Y :=
  sorry

/-- Membership in the image of finite-type points along a surjective
locally-of-finite-type morphism is equivalent to being a finite-type point of
the target. -/
theorem mem_image_finiteTypePoints_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [LocallyOfFiniteType f] [Surjective f]
    {y : Points Y} :
    y ∈ Points.map f '' finiteTypePoints X ↔ y ∈ finiteTypePoints Y :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
