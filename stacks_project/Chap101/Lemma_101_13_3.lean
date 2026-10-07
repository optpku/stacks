module

public import stacks_project.Chap101.Lemma_101_13_3_UniversallyClosed

/-!
# Base change of universally closed morphisms of algebraic stacks

The base change of a universally closed morphism of algebraic stacks by any
morphism of algebraic stacks is universally closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.13.3: The base change of a universally closed morphism of algebraic
stacks by any morphism of algebraic stacks is universally closed.

Stacks writes the base change as `Z ×_Y X ⟶ Z`; the Lean projection is
`TwoFibreProduct.snd f g`. -/
@[stacks 0514]
instance universallyClosed_pullback_snd {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (f : X ⟶ Y) (g : Z ⟶ Y) [UniversallyClosed f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    UniversallyClosed (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
