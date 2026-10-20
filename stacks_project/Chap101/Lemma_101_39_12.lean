module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.39.12: The composition of morphisms of algebraic stacks which
satisfy the existence part of the valuative criterion again satisfies the
existence part of the valuative criterion. -/
@[stacks 0CLM] #check
  (AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Existence.comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S},
      [AlgebraicGeometry.AlgebraicStack X] → [AlgebraicGeometry.AlgebraicStack Y] →
      [AlgebraicGeometry.AlgebraicStack Z] →
      (f : X ⟶ Y) → (g : Y ⟶ Z) →
      [AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Existence f] →
      [AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Existence g] →
      AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Existence (f ≫ g))
