/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedPoints.Impurity

open CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.Impurity :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    X.Modules → (X ⟶ Y) → AlgebraicGeometry.AlgebraicSpace.Points Y → Type (u + 1))
