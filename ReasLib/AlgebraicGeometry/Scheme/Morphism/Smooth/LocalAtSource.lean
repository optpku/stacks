/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtSource.AffineDescent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Descent

/-!
# Source locality of smooth scheme morphisms

This file records that smoothness of scheme morphisms is local on the source for the smooth
precoverage.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Smooth

/-- Smoothness of scheme morphisms is local on the source for the smooth precoverage. -/
instance isLocalAtSourceSmooth :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.Smooth :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSmoothPrecoverage := sorry

end AlgebraicGeometry.Smooth
