module

public import stacks_project.Chap101.Lemma_101_37_2_BaseChange

/-!
# Base change of proper morphisms of algebraic stacks

A base change of a proper morphism of algebraic stacks is proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Proper

/-- Lemma 101.37.2: A base change of a proper morphism is proper.

Stacks writes the base change as `Y' ×_Y X ⟶ Y'`; the Lean projection is
`TwoFibreProduct.snd f g` of a proper morphism `f : X ⟶ Y` along a test
morphism `g : Z ⟶ Y`. -/
@[stacks 0CL6]
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Proper f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Proper (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Proper
