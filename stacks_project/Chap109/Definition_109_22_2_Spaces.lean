/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Stable

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Stable morphisms of algebraic spaces. -/
#check (AlgebraicGeometry.AlgebraicSpace.IsStableFamily :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)
