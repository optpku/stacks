module

public import stacks_project.Chap101.Lemma_101_36_3_BaseChange

/-!
# Base change of unramified morphisms of algebraic stacks

A base change of an unramified morphism of algebraic stacks is unramified.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Unramified

/-- Lemma 101.36.3: A base change of an unramified morphism is unramified.

Stacks writes the base change as `Y' ×_Y X ⟶ Y'`; the Lean projection is
`TwoFibreProduct.snd f g` of an unramified morphism `f : X ⟶ Y` along a test
morphism `g : Z ⟶ Y`. -/
@[stacks 0CIV]
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Unramified f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Unramified (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Unramified
