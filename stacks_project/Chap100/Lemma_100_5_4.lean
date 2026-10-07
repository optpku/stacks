module

public import stacks_project.Chap100.Lemma_100_5_4_Descent

/-!
# Descent of surjectivity along a 2-fibre product of algebraic stacks

If the base change of a morphism of algebraic stacks along a surjective
morphism is surjective, then the original morphism is surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Surjective

/-- Lemma 100.5.4: Let `f : X ⟶ Y` be a morphism of algebraic stacks. Let
`g : Z ⟶ Y` be a surjective morphism of algebraic stacks. If the base change
`TwoFibreProduct.snd f g` of `f` is surjective, then `f` is surjective.

Stacks writes the base change as `Y' ×_Y X ⟶ Y'`; Lean's chosen projection is
`TwoFibreProduct.snd f g` for `f : X ⟶ Y` along `g : Z ⟶ Y`. -/
@[stacks 06PM]
theorem of_twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Surjective g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    [Surjective (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)] :
    Surjective f :=
  sorry

/-- After base change along a surjective morphism of algebraic stacks, the
original morphism is surjective if and only if `TwoFibreProduct.snd f g` is
surjective. -/
theorem twoFibreProduct_snd_iff {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Surjective g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Surjective (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) ↔ Surjective f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Surjective
