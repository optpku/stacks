/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_10_2_Integral

/-!
# Base change of integral and finite morphisms of algebraic stacks

The base change of an integral (resp. finite) morphism of algebraic stacks by
any morphism of algebraic stacks is integral (resp. finite).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsIntegralHom

/-- Lemma 101.10.2 (1): Let `X ⟶ Y` be a morphism of algebraic stacks. Let
`Z ⟶ Y` be an integral morphism of algebraic stacks. Then
`Z ×_Y X ⟶ X` is an integral morphism of algebraic stacks.

Stacks writes the base change as `Z ×_Y X ⟶ X`; the Lean projection is
`TwoFibreProduct.fst f g` for `g : Z ⟶ Y`. -/
@[stacks 0CHV]
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsIntegralHom g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    IsIntegralHom (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsIntegralHom

namespace AlgebraicGeometry.AlgebraicStack.IsFinite

/-- Lemma 101.10.2 (2): Let `X ⟶ Y` be a morphism of algebraic stacks. Let
`Z ⟶ Y` be a finite morphism of algebraic stacks. Then
`Z ×_Y X ⟶ X` is a finite morphism of algebraic stacks.

Stacks writes the base change as `Z ×_Y X ⟶ X`; the Lean projection is
`TwoFibreProduct.fst f g` for `g : Z ⟶ Y`. -/
@[stacks 0CHV]
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsFinite g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    IsFinite (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsFinite
