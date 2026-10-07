module

public import stacks_project.Chap101.Lemma_101_14_3_UniversallyInjective

/-!
# Base change of universally injective morphisms of algebraic stacks

The base change of a universally injective morphism of algebraic stacks by any
morphism of algebraic stacks is universally injective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.14.3: The base change of a universally injective morphism of algebraic
stacks by any morphism of algebraic stacks is universally injective.

Stacks writes the base change as `Z ×_Y X ⟶ Z`; the Lean projection is
`TwoFibreProduct.snd f g`. -/
@[stacks 0CI3]
instance universallyInjective_pullback_snd {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (f : X ⟶ Y) (g : Z ⟶ Y) [UniversallyInjective f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    UniversallyInjective (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
