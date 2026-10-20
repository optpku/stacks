module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.UniversallyClosed
import StacksCheckRecall

/-!
# Valuative criterion for universal closedness

A quasi-compact morphism of algebraic stacks that satisfies the existence part
of the valuative criterion is universally closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.42.1: A quasi-compact morphism of algebraic stacks that satisfies
the existence part of the valuative criterion is universally closed. -/
@[stacks 0CLW] #check
  (AlgebraicGeometry.AlgebraicStack.UniversallyClosed.of_quasiCompact_of_existence :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.GroupoidsOver S}
      [AlgebraicGeometry.AlgebraicStack X] [AlgebraicGeometry.AlgebraicStack Y]
      (f : X ⟶ Y), [AlgebraicGeometry.AlgebraicStack.QuasiCompact f] →
      [AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Existence f] →
      AlgebraicGeometry.AlgebraicStack.UniversallyClosed f)
