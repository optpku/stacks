/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.Divisor

@[expose] public section

#check (AlgebraicGeometry.CycleGroup.flatDivisorDegree :
  ∀ (n : ℤ) (r : ℕ), (n - 1) + (r : ℤ) = n + (r : ℤ) - 1)
