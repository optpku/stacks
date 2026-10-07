module

public import stacks_project.Chap67.Lemma_67_41_7_Pullback

/-!
# Base change of the valuative criterion for morphisms of algebraic spaces

The base change of a morphism of algebraic spaces which satisfies the existence
part of (resp. uniqueness part of) the valuative criterion by any morphism of
algebraic spaces satisfies the existence part of (resp. uniqueness part of) the
valuative criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.41.7 (1): The base change of a morphism of algebraic spaces which
satisfies the existence part of the valuative criterion by any morphism of
algebraic spaces satisfies the existence part of the valuative criterion. -/
@[stacks 03IY]
instance valuativeCriterionExistence_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@ValuativeCriterion.Existence S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- Lemma 67.41.7 (2): The base change of a morphism of algebraic spaces which
satisfies the uniqueness part of the valuative criterion by any morphism of
algebraic spaces satisfies the uniqueness part of the valuative criterion. -/
@[stacks 03IY]
instance valuativeCriterionUniqueness_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@ValuativeCriterion.Uniqueness S : MorphismProperty (AlgebraicSpace S)) := sorry

#check ValuativeCriterion.Existence.of_isPullback
#check ValuativeCriterion.Uniqueness.of_isPullback

end AlgebraicGeometry.AlgebraicSpace
