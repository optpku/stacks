/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocalCompleteIntersection
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Definition 101.44.1: a morphism `f : X ⟶ Y` of algebraic stacks is
a local complete intersection morphism, or Koszul, if the equivalent
conditions of Lemma 101.16.1 hold with `P` = local complete intersection. -/
@[stacks 0CJ3] #check (AlgebraicGeometry.AlgebraicStack.IsLocalCompleteIntersection :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y],
    (X ⟶ Y) → Prop)
