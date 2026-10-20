/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Relative morphism pairs

The displayed pairs `(a, b)` for morphisms of algebraic spaces over a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- 97.10.0.1: for morphisms `Z ⟶ B` and `X ⟶ B` of algebraic spaces over a
scheme `S`, a test scheme `T` over `S` determines pairs `(a, b)` with
`a : ofOver T ⟶ B` and `b` a morphism over `ofOver T` from `pullback a z` to
`pullback a x`. -/
@[stacks 05Y1] #check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.Pair :
  ∀ {S : Scheme.{u}} {B Z X : AlgebraicSpace S},
    (Z ⟶ B) → (X ⟶ B) → Over S → Type (u + 1))
