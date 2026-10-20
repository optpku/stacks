/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Dimension

open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicCycle.dimensionSubgroup :
  {X : Scheme.{u}} → (X → ℤ) → ℤ → AddSubgroup (AlgebraicGeometry.AlgebraicCycle X ℤ))
