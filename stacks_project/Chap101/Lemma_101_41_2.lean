module

public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Lemma_101_39_8_Uniqueness

/-!
# Quasi-separated morphisms with uniqueness are separated

A quasi-separated morphism of algebraic stacks that satisfies uniqueness in the
valuative criterion is separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Separated

/-- Lemma 101.41.2: If `f : X ⟶ Y` is a quasi-separated morphism of algebraic
stacks and `f` satisfies the uniqueness part of the valuative criterion, then
`f` is separated. -/
@[stacks 0CLT]
theorem of_valuativeCriterion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [QuasiSeparated f] [ValuativeCriterion.Uniqueness f] : Separated f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Separated
