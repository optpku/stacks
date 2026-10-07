module

public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
public import stacks_project.Chap101.Lemma_101_39_12_Existence

/-!
# Existence for representable morphisms of algebraic stacks

A morphism of algebraic stacks representable by algebraic spaces satisfies the
existence part of the valuative criterion if and only if every scheme-slice
representing morphism of algebraic spaces does.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack
namespace ValuativeCriterion.Existence

/-- Lemma 101.39.13: Let `f : X ⟶ Y` be a morphism of algebraic stacks which is
representable by algebraic spaces. Then `f` satisfies the existence part of
the valuative criterion if and only if for every scheme `T` and morphism
`T ⟶ Y` the morphism `X ×_Y T ⟶ T` satisfies the existence part of the
valuative criterion as a morphism of algebraic spaces. -/
@[stacks 0CLN]
theorem iff_has {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    Existence f ↔
      Groupoids.Hom.has (@AlgebraicSpace.ValuativeCriterion.Existence S) f :=
  sorry

/-- A morphism of algebraic stacks representable by algebraic spaces that has
existence on every scheme-slice representing morphism of algebraic spaces
satisfies existence. -/
theorem of_has {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    (h : Groupoids.Hom.has (@AlgebraicSpace.ValuativeCriterion.Existence S) f) :
    Existence f :=
  sorry

/-- A morphism of algebraic stacks representable by algebraic spaces that
satisfies existence has existence on every scheme-slice representing morphism
of algebraic spaces. -/
theorem has_of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    [Existence f] :
    Groupoids.Hom.has (@AlgebraicSpace.ValuativeCriterion.Existence S) f :=
  sorry

/-- Existence of a representable morphism of algebraic stacks is equivalent to
existence of every scheme-slice representing morphism of algebraic spaces. -/
theorem iff_forall {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    Existence f ↔
      ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y) (Fy : AlgebraicSpace S)
        (fy : Fy ⟶ AlgebraicSpace.ofOver U),
        RepresentsBaseChange f y Fy fy →
          AlgebraicSpace.ValuativeCriterion.Existence fy :=
  sorry

end ValuativeCriterion.Existence
end AlgebraicGeometry.AlgebraicStack
