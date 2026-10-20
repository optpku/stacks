/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.InDimensions

open CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.flatOverInDimensionsGE :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    X.Modules → (X ⟶ Y) → ℕ → Prop)
