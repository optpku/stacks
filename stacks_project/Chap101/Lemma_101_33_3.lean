/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth.BaseChange

/-!
# Base change of smooth morphisms of algebraic stacks

A base change of a smooth morphism of algebraic stacks is smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

/- Lemma 101.33.3: A base change of a smooth morphism is smooth. -/
@[stacks 075W] #check (AlgebraicGeometry.AlgebraicStack.Smooth.twoFibreProduct_snd :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [AlgebraicStack.Smooth f],
    AlgebraicStack.Smooth (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

#check (AlgebraicGeometry.AlgebraicStack.Smooth.of_isBilimit :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [AlgebraicStack.Smooth f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit),
    AlgebraicStack.Smooth c.snd)

#check (AlgebraicGeometry.AlgebraicStack.Smooth.twoFibreProduct_fst :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [AlgebraicStack.Smooth g],
    AlgebraicStack.Smooth (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g))
