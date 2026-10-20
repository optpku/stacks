module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.ClosedImmersion
import StacksCheckRecall

/-!
# Closed immersions of algebraic stacks and the valuative criterion

A closed immersion of algebraic stacks satisfies both the existence part and
the uniqueness part of the valuative criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.39.14 (1): A closed immersion of algebraic stacks satisfies the
existence part of the valuative criterion. -/
@[stacks 0CLP]
#check (AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Existence.of_closedImmersion :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Groupoids.Hom.ClosedImmersion f],
    AlgebraicStack.ValuativeCriterion.Existence f)

/- Lemma 101.39.14 (2): A closed immersion of algebraic stacks satisfies the
uniqueness part of the valuative criterion. -/
@[stacks 0CLP]
#check (AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Uniqueness.of_closedImmersion :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Groupoids.Hom.ClosedImmersion f],
    AlgebraicStack.ValuativeCriterion.Uniqueness f)
