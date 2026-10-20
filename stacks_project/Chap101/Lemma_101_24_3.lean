/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiFinite.BaseChange
import StacksCheckRecall

/-!
# Base change of quasi-finite morphisms of algebraic stacks

A base change of a quasi-finite morphism of algebraic stacks is
quasi-finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

/- Lemma 101.24.3: A base change of a quasi-finite morphism is
quasi-finite.

Stacks writes the base change as `Y' ×_Y X ⟶ Y'`; the Lean projection is
`TwoFibreProduct.snd f g` of a quasi-finite morphism `f : X ⟶ Y`
along a test morphism `g : Z ⟶ Y`. -/
@[stacks 0G2P] #check
  (AlgebraicGeometry.AlgebraicStack.QuasiFinite.twoFibreProduct_snd :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [AlgebraicStack.QuasiFinite f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
    AlgebraicStack.QuasiFinite
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

#check (AlgebraicGeometry.AlgebraicStack.QuasiFinite.of_isBilimit :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [AlgebraicStack.QuasiFinite f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit),
    AlgebraicStack.QuasiFinite c.snd)

#check (AlgebraicGeometry.AlgebraicStack.QuasiFinite.twoFibreProduct_fst :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [AlgebraicStack.QuasiFinite g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
    AlgebraicStack.QuasiFinite
      (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g))
