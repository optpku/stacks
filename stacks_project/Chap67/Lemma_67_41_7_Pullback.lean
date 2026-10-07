module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion

/-!
# Base change of the valuative criterion for morphisms of algebraic spaces

The existence part and the uniqueness part of the valuative criterion are each
stable under arbitrary base change. This module records the morphism-level
pullback companions for the existing `ValuativeCriterion.Existence` and
`ValuativeCriterion.Uniqueness` classes from Definition 67.41.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ValuativeCriterion.Existence

/-- Morphisms of algebraic spaces satisfying the existence part of the valuative
criterion are stable under pullback along an arbitrary morphism, expressed by an
`IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : ValuativeCriterion.Existence g) :
    ValuativeCriterion.Existence g' := sorry

/-- The base-change projection `pullback.snd f g` of a morphism `f : X ⟶ Y`
satisfying the existence part of the valuative criterion also satisfies the
existence part. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : ValuativeCriterion.Existence f) (g : Z ⟶ Y) [HasPullback f g] :
    ValuativeCriterion.Existence (pullback.snd f g) := sorry

end ValuativeCriterion.Existence

/-- Typeclass form of base-change stability for the existence part of the
valuative criterion along a morphism for which the pullback exists. -/
instance valuativeCriterionExistence_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [ValuativeCriterion.Existence f] [HasPullback f g] :
    ValuativeCriterion.Existence (pullback.snd f g) := sorry

namespace ValuativeCriterion.Uniqueness

/-- Morphisms of algebraic spaces satisfying the uniqueness part of the valuative
criterion are stable under pullback along an arbitrary morphism, expressed by an
`IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : ValuativeCriterion.Uniqueness g) :
    ValuativeCriterion.Uniqueness g' := sorry

/-- The base-change projection `pullback.snd f g` of a morphism `f : X ⟶ Y`
satisfying the uniqueness part of the valuative criterion also satisfies the
uniqueness part. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : ValuativeCriterion.Uniqueness f) (g : Z ⟶ Y) [HasPullback f g] :
    ValuativeCriterion.Uniqueness (pullback.snd f g) := sorry

end ValuativeCriterion.Uniqueness

/-- Typeclass form of base-change stability for the uniqueness part of the
valuative criterion along a morphism for which the pullback exists. -/
instance valuativeCriterionUniqueness_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [ValuativeCriterion.Uniqueness f] [HasPullback f g] :
    ValuativeCriterion.Uniqueness (pullback.snd f g) := sorry

end AlgebraicGeometry.AlgebraicSpace
