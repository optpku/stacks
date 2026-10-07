module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion

/-!
# Composition of the valuative criterion for morphisms of algebraic spaces

The existence part and the uniqueness part of the valuative criterion are each
stable under composition of morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.41.8 (1): The composition of two morphisms of algebraic spaces which
satisfy the existence part of the valuative criterion satisfies the existence
part of the valuative criterion. -/
@[stacks 03IZ]
instance valuativeCriterionExistence_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@ValuativeCriterion.Existence S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of morphisms of algebraic spaces satisfying the existence
part of the valuative criterion satisfies the existence part. -/
instance valuativeCriterionExistence_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [ValuativeCriterion.Existence f] [ValuativeCriterion.Existence g] :
    ValuativeCriterion.Existence (f ≫ g) := sorry

/-- Lemma 67.41.8 (2): The composition of two morphisms of algebraic spaces which
satisfy the uniqueness part of the valuative criterion satisfies the uniqueness
part of the valuative criterion. -/
@[stacks 03IZ]
instance valuativeCriterionUniqueness_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@ValuativeCriterion.Uniqueness S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of morphisms of algebraic spaces satisfying the uniqueness
part of the valuative criterion satisfies the uniqueness part. -/
instance valuativeCriterionUniqueness_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [ValuativeCriterion.Uniqueness f] [ValuativeCriterion.Uniqueness g] :
    ValuativeCriterion.Uniqueness (f ≫ g) := sorry

end AlgebraicGeometry.AlgebraicSpace
