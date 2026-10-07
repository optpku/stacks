module

public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
public import stacks_project.Chap101.Lemma_101_39_8_Uniqueness

/-!
# Uniqueness for representable morphisms of algebraic stacks

A morphism of algebraic stacks representable by algebraic spaces satisfies the
uniqueness part of the valuative criterion if and only if every scheme-slice
representing morphism of algebraic spaces does.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory
open AlgebraicSpace.ValuativeCriterion renaming Uniqueness → SpaceUniqueness

universe u

namespace AlgebraicGeometry.AlgebraicStack
namespace ValuativeCriterion
namespace Uniqueness

/-- Lemma 101.39.9: Let `f : X ⟶ Y` be a morphism of algebraic stacks which is
representable by algebraic spaces. Then `f` satisfies the uniqueness part of
the valuative criterion if and only if for every scheme `T` and morphism
`T ⟶ Y` the morphism `X ×_Y T ⟶ T` satisfies the uniqueness part of the
valuative criterion as a morphism of algebraic spaces. -/
@[stacks 0CLJ]
theorem iff_has {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    Uniqueness f ↔
      Groupoids.Hom.has (@SpaceUniqueness S) f :=
  sorry

/-- A morphism of algebraic stacks representable by algebraic spaces that has
uniqueness on every scheme-slice representing morphism of algebraic spaces
satisfies uniqueness. -/
theorem of_has {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    (h : Groupoids.Hom.has (@SpaceUniqueness S) f) :
    Uniqueness f :=
  sorry

/-- A morphism of algebraic stacks representable by algebraic spaces that
satisfies uniqueness has uniqueness on every scheme-slice representing morphism
of algebraic spaces. -/
theorem has_of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    [Uniqueness f] :
    Groupoids.Hom.has (@SpaceUniqueness S) f :=
  sorry

/-- Uniqueness of a representable morphism of algebraic stacks is equivalent to
uniqueness of every scheme-slice representing morphism of algebraic spaces. -/
theorem iff_forall {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    Uniqueness f ↔
      ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y) (Fy : AlgebraicSpace S)
        (fy : Fy ⟶ AlgebraicSpace.ofOver U),
        RepresentsBaseChange f y Fy fy →
          SpaceUniqueness fy :=
  sorry

/-- Uniqueness of a morphism of algebraic stacks transports to uniqueness of a
scheme-slice representing morphism of algebraic spaces. -/
theorem of_represents {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [Uniqueness f]
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U} (h : RepresentsBaseChange f y Fy fy) :
    SpaceUniqueness fy :=
  sorry

end Uniqueness
end ValuativeCriterion
end AlgebraicGeometry.AlgebraicStack
