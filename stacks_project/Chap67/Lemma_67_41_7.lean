module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.BaseChange
import StacksCheckRecall

/-!
# Base change of the valuative criterion for morphisms of algebraic spaces

The base change of a morphism of algebraic spaces which satisfies the existence
part of (resp. uniqueness part of) the valuative criterion by any morphism of
algebraic spaces satisfies the existence part of (resp. uniqueness part of) the
valuative criterion.
-/

@[expose] public section

universe u

/- Lemma 67.41.7 (existence): The existence part of the valuative criterion is
stable under arbitrary base change of algebraic spaces. -/
@[stacks 03IY] #check
  (AlgebraicGeometry.AlgebraicSpace.valuativeCriterionExistence_isStableUnderBaseChange :
    ∀ {S : AlgebraicGeometry.Scheme.{u}},
      CategoryTheory.MorphismProperty.IsStableUnderBaseChange
        (@AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Existence S :
          CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))

/- Lemma 67.41.7 (uniqueness): The uniqueness part of the valuative criterion is
stable under arbitrary base change of algebraic spaces. -/
@[stacks 03IY] #check
  (AlgebraicGeometry.AlgebraicSpace.valuativeCriterionUniqueness_isStableUnderBaseChange :
    ∀ {S : AlgebraicGeometry.Scheme.{u}},
      CategoryTheory.MorphismProperty.IsStableUnderBaseChange
        (@AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Uniqueness S :
          CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))
