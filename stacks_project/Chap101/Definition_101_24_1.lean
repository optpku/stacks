/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiFinite
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 101.24.1: a morphism `f : X ⟶ Y` of algebraic stacks is
quasi-finite if it is locally quasi-finite and quasi-compact. -/
@[stacks 0G2M] #check (AlgebraicGeometry.AlgebraicStack.QuasiFinite :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.GroupoidsOver S}
    [AlgebraicGeometry.AlgebraicStack X] [AlgebraicGeometry.AlgebraicStack Y],
    (X ⟶ Y) → Prop)
