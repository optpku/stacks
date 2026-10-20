/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Pointwise

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.ChowGroup.Pointwise

/- Remark 42.19.2: the pointwise differential is the locally finite sum of
pushed-forward principal divisors on reduced point closures. -/
#check (boundaryHom :
  ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (d : X → ℤ) [IsDimensionFunction d] (k : ℤ),
    locallyFinite d (k + 1) →+ CycleGroup X d k)

#check (complex :
  ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (d : X → ℤ) [IsDimensionFunction d] (k : ℤ),
    ShortComplex Ab)

end AlgebraicGeometry.ChowGroup.Pointwise
