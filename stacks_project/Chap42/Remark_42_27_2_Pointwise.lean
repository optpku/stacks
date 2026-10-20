/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.MilnorComplex

open AlgebraicGeometry CategoryTheory

universe u

/- Compatibility bridge for the pointwise locally finite Milnor complex. -/
#check (AlgebraicGeometry.ChowGroup.Pointwise.milnorComplex :
  ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
    (d : X → ℤ) [IsDimensionFunction d] (k : ℤ), ShortComplex Ab)
