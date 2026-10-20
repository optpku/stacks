/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Stratification

open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.stratumPoints :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S},
    (ℕ → AlgebraicGeometry.AlgebraicSpace.OpenSubspace X) → ℕ →
      Set (AlgebraicGeometry.AlgebraicSpace.Points X))
