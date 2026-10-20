/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteType.BaseChange
import StacksCheckRecall

/-!
# Base change of finite type morphisms of algebraic stacks

A base change of a finite type morphism of algebraic stacks is of finite
type. The same holds for locally of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

/- Lemma 101.17.3: A base change of a finite type morphism of algebraic stacks
is of finite type. The same holds for locally of finite type. -/
@[stacks 06FU] #check
  (AlgebraicGeometry.AlgebraicStack.FiniteType.twoFibreProduct_snd :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Z ⟶ Y) [AlgebraicStack.FiniteType f]
      [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
      AlgebraicStack.FiniteType (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

#check
  (AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType.twoFibreProduct_snd :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Z ⟶ Y) [AlgebraicStack.LocallyOfFiniteType f]
      [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
      AlgebraicStack.LocallyOfFiniteType
        (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))
