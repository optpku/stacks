module

public import stacks_project.Chap101.Lemma_101_11_3_UniversallyOpen

/-!
# Base change of universally open morphisms of algebraic stacks

The base change of a universally open morphism of algebraic stacks by any
morphism of algebraic stacks is universally open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.11.3: The base change of a universally open morphism of algebraic
stacks by any morphism of algebraic stacks is universally open.

Stacks writes the base change as `Z ×_Y X ⟶ Z`; the Lean projection is
`TwoFibreProduct.snd f g`. -/
@[stacks 06U3]
instance universallyOpen_pullback_snd {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (f : X ⟶ Y) (g : Z ⟶ Y) [UniversallyOpen f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    UniversallyOpen (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
