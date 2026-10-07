module

public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Lemma_101_39_8_Uniqueness

/-!
# Separated morphisms satisfy uniqueness in the valuative criterion

A separated morphism of algebraic stacks has a thin dotted-arrow category with
at most one isomorphism class in every solid valuative square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.ValuativeCriterion

/-- Lemma 101.41.3: If `f : X ⟶ Y` is a separated morphism of algebraic stacks,
then `f` satisfies the uniqueness part of the valuative criterion. -/
@[stacks 0CLU]
instance Uniqueness.of_separated {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Separated f] :
    Uniqueness f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.ValuativeCriterion
