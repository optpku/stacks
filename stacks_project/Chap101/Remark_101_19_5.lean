/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.AutomorphismGroup
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Remark 101.19.5
Let `f : X ⟶ Y` be a morphism of algebraic stacks. Let `x ∈ |X|` be a point.
To indicate the equivalent conditions of Lemma 101.19.4 are satisfied for `f`
and `x` in the literature the terminology `f` is stabilizer preserving at `x`
or `f` is fixed-point reflecting at `x` is used. We prefer to say `f` induces
an isomorphism between automorphism groups at `x` and `f(x)`.
-/
@[stacks 0DTW] #check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.IsIsoAt :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y], (X ⟶ Y) → |X| → Prop)
