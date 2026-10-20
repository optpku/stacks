/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteType
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Definition 101.17.1 (1): a morphism `f : X ⟶ Y` of algebraic stacks is
locally of finite type if the equivalent conditions of Lemma 101.16.1 hold
with `P` = locally of finite type. -/
@[stacks 06FS] #check (AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y],
    (X ⟶ Y) → Prop)

/- Definition 101.17.1 (2): a morphism `f : X ⟶ Y` of algebraic stacks is
of finite type if it is locally of finite type and quasi-compact. -/
@[stacks 06FS] #check (AlgebraicGeometry.AlgebraicStack.FiniteType :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y],
    (X ⟶ Y) → Prop)
