module

public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_13_2_Closed
public import stacks_project.Chap101.Lemma_101_39_12_Existence

/-!
# Valuative criterion for universal closedness

A quasi-separated universally closed morphism of algebraic stacks satisfies the
existence part of the valuative criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.ValuativeCriterion

/-- Lemma 101.42.2: A quasi-separated universally closed morphism of algebraic
stacks satisfies the existence part of the valuative criterion. -/
@[stacks 0CLX]
instance Existence.of_universallyClosed {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [QuasiSeparated f] [UniversallyClosed f] : Existence f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.ValuativeCriterion
