/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 101.23.2: a morphism `f : X ⟶ Y` of algebraic stacks is
locally quasi-finite if it is quasi-DM, locally of finite type, and for
every morphism `Spec(k) ⟶ Y` where `k` is a field the space `|X_k|` is
discrete. -/
@[stacks 06PU] #check (AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y],
    (X ⟶ Y) → Prop)
