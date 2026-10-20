module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Uniqueness

/-!
# Closed immersions of algebraic stacks and the valuative criterion

A closed immersion of algebraic stacks satisfies both the existence part and
the uniqueness part of the valuative criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.ValuativeCriterion

/-- A closed immersion of algebraic stacks satisfies the existence part of the
valuative criterion. -/
instance Existence.of_closedImmersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [ClosedImmersion f] :
    Existence f :=
  sorry

/-- A closed immersion of algebraic stacks satisfies the uniqueness part of the
valuative criterion. -/
instance Uniqueness.of_closedImmersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [ClosedImmersion f] :
    Uniqueness f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.ValuativeCriterion
