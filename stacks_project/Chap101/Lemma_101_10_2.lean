/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.Finite.BaseChange
import StacksCheckRecall

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

/- Lemma 101.10.2 (1): Let `X ⟶ Y` be a morphism of algebraic stacks. Let
`Z ⟶ Y` be an integral morphism of algebraic stacks. Then
`Z ×_Y X ⟶ X` is an integral morphism of algebraic stacks.

Stacks writes the base change as `Z ×_Y X ⟶ X`; the Lean projection is
`TwoFibreProduct.fst f g` for `g : Z ⟶ Y`. -/
@[stacks 0CHV] #check
  (AlgebraicGeometry.AlgebraicStack.IsIntegralHom.twoFibreProduct_fst :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Z ⟶ Y) [AlgebraicGeometry.AlgebraicStack.IsIntegralHom g],
      AlgebraicGeometry.AlgebraicStack.IsIntegralHom
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g))

/- Lemma 101.10.2 (2): Let `X ⟶ Y` be a morphism of algebraic stacks. Let
`Z ⟶ Y` be a finite morphism of algebraic stacks. Then
`Z ×_Y X ⟶ X` is a finite morphism of algebraic stacks.

Stacks writes the base change as `Z ×_Y X ⟶ X`; the Lean projection is
`TwoFibreProduct.fst f g` for `g : Z ⟶ Y`. -/
@[stacks 0CHV] #check
  (AlgebraicGeometry.AlgebraicStack.IsFinite.twoFibreProduct_fst :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Z ⟶ Y) [AlgebraicGeometry.AlgebraicStack.IsFinite g],
      AlgebraicGeometry.AlgebraicStack.IsFinite
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g))
