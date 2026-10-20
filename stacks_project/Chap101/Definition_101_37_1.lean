/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 101.37.1: a morphism `f : X ⟶ Y` of algebraic stacks is
proper if it is separated, finite type, and universally closed. -/
@[stacks 0CL5] #check (AlgebraicGeometry.AlgebraicStack.Proper :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.GroupoidsOver S}
    [AlgebraicGeometry.AlgebraicStack X] [AlgebraicGeometry.AlgebraicStack Y],
    (X ⟶ Y) → Prop)
