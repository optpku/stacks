module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.BaseChange
import StacksCheckRecall

/-!
# Base change of the existence part of the valuative criterion

The base change of a morphism of algebraic stacks which satisfies the
existence part of the valuative criterion by any morphism of algebraic
stacks again satisfies the existence part of the valuative criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.ValuativeCriterion

/- Lemma 101.39.11: The base change of a morphism of algebraic stacks which
satisfies the existence part of the valuative criterion by any morphism of
algebraic stacks is a morphism of algebraic stacks which satisfies the
existence part of the valuative criterion.

Stacks writes the base change as `Y' ×_Y X ⟶ Y'`; the Lean projection is
`TwoFibreProduct.snd f g` of a morphism `f : X ⟶ Y` satisfying existence
along a test morphism `g : Z ⟶ Y`. -/
@[stacks 0CLL]
#check (AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Existence.twoFibreProduct_snd :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Existence f],
    Existence (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

end AlgebraicGeometry.AlgebraicStack.ValuativeCriterion
