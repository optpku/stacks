/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Open.Locality

@[expose] public section

universe u

namespace AlgebraicGeometry.UniversallyOpen

/-- Universal openness of scheme morphisms is local on the source for the fppf
precoverage. -/
instance isLocalAtSourceFppf :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.UniversallyOpen :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage := sorry

end AlgebraicGeometry.UniversallyOpen
