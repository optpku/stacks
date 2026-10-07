module

public import stacks_project.Chap101.Lemma_101_33_3_BaseChange

/-!
# Base change of smooth morphisms of algebraic stacks

A base change of a smooth morphism of algebraic stacks is smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Smooth

/-- Lemma 101.33.3: A base change of a smooth morphism is smooth.

Stacks writes the base change as `Y' ×_Y X ⟶ Y'`; the Lean projection is
`TwoFibreProduct.snd f g` of a smooth morphism `f : X ⟶ Y` along a test
morphism `g : Z ⟶ Y`. -/
@[stacks 075W]
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Smooth f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Smooth (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Smooth
