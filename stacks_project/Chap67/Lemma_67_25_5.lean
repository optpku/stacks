module

public import stacks_project.Chap67.Lemma_67_25_4_FiniteTypePoint
public import stacks_project.Chap67.Definition_67_5_2_Surjective

/-!
# Images of finite type points under surjective locally finite type morphisms

A surjective locally-of-finite-type morphism of algebraic spaces sends finite-type
points onto finite-type points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType

/-- Lemma 67.25.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is locally of finite type and surjective, then
`Points.map f '' finiteTypePoints X = finiteTypePoints Y`. -/
@[stacks 06EJ]
theorem image_finiteTypePoints_eq_of_surjective {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [Surjective f] :
    Points.map f '' finiteTypePoints X = finiteTypePoints Y :=
  sorry

/-- Membership in the image of finite-type points along a surjective
locally-of-finite-type morphism is equivalent to being a finite-type point of
the target. -/
theorem mem_image_finiteTypePoints_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [Surjective f] {y : Points Y} :
    y ∈ Points.map f '' finiteTypePoints X ↔ y ∈ finiteTypePoints Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType
