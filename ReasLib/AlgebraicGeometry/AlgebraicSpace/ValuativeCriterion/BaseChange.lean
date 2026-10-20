module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion

/-!
# Base change of the valuative criterion for algebraic spaces

The existence and uniqueness parts of the valuative criterion for morphisms of
algebraic spaces are each stable under arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The existence part of the valuative criterion for morphisms of algebraic
spaces is stable under arbitrary base change. -/
instance valuativeCriterionExistence_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@ValuativeCriterion.Existence S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The uniqueness part of the valuative criterion for morphisms of algebraic
spaces is stable under arbitrary base change. -/
instance valuativeCriterionUniqueness_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@ValuativeCriterion.Uniqueness S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The second pullback projection of a morphism satisfying the existence part
of the valuative criterion also satisfies the existence part. -/
instance valuativeCriterionExistence_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [ValuativeCriterion.Existence f] [HasPullback f g] :
    ValuativeCriterion.Existence (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g (inferInstance : ValuativeCriterion.Existence f)

/-- The second pullback projection of a morphism satisfying the uniqueness part
of the valuative criterion also satisfies the uniqueness part. -/
instance valuativeCriterionUniqueness_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [ValuativeCriterion.Uniqueness f] [HasPullback f g] :
    ValuativeCriterion.Uniqueness (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g (inferInstance : ValuativeCriterion.Uniqueness f)

end AlgebraicGeometry.AlgebraicSpace
