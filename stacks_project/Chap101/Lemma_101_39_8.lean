module

public import stacks_project.Chap101.Lemma_101_39_8_Uniqueness
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 101.39.8: the composition of morphisms of algebraic stacks which
satisfy the uniqueness part of the valuative criterion is another morphism
of algebraic stacks which satisfies the uniqueness part of the valuative
criterion. -/
@[stacks 0CLI] #check
  (ValuativeCriterion.Uniqueness.comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [ValuativeCriterion.Uniqueness f] [ValuativeCriterion.Uniqueness g],
      ValuativeCriterion.Uniqueness (f ≫ g))
