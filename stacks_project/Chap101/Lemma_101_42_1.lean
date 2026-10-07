module

public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap101.Definition_101_13_2_Closed
public import stacks_project.Chap101.Lemma_101_39_12_Existence

/-!
# Valuative criterion for universal closedness

A quasi-compact morphism of algebraic stacks that satisfies the existence part
of the valuative criterion is universally closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.UniversallyClosed

/-- Lemma 101.42.1: A quasi-compact morphism of algebraic stacks that satisfies
the existence part of the valuative criterion is universally closed. -/
@[stacks 0CLW]
instance of_quasiCompact_of_existence {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [QuasiCompact f] [ValuativeCriterion.Existence f] : UniversallyClosed f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.UniversallyClosed
