module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Uniqueness.Representable
import StacksCheckRecall

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

/- Lemma 101.39.9: Let `f : X ⟶ Y` be a morphism of algebraic stacks which is
representable by algebraic spaces. Then `f` satisfies the uniqueness part of
the valuative criterion if and only if for every scheme `T` and morphism
`T ⟶ Y` the morphism `X ×_Y T ⟶ T` satisfies the uniqueness part of the
valuative criterion as a morphism of algebraic spaces. -/
@[stacks 0CLJ] #check
  (AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Uniqueness.iff_has :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f),
    Uniqueness f ↔
      Groupoids.Hom.has (@SpaceUniqueness S) f)

#check
  (AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Uniqueness.of_has :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    (h : Groupoids.Hom.has (@SpaceUniqueness S) f),
    Uniqueness f)

#check
  (AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Uniqueness.has_of :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    [Uniqueness f],
    Groupoids.Hom.has (@SpaceUniqueness S) f)

#check
  (AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Uniqueness.iff_forall :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f),
    Uniqueness f ↔
      ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y) (Fy : AlgebraicSpace S)
        (fy : Fy ⟶ AlgebraicSpace.ofOver U),
        RepresentsBaseChange f y Fy fy →
          SpaceUniqueness fy)

#check
  (AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Uniqueness.of_represents :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [Uniqueness f]
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U} (h : RepresentsBaseChange f y Fy fy),
    SpaceUniqueness fy)

end Uniqueness
end ValuativeCriterion
end AlgebraicGeometry.AlgebraicStack
