/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtSource.AffineDescent

/-!
# Locality of local finite type

This file records that local finite type of scheme morphisms is local on the source for
fppf covers.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.LocallyOfFiniteType

/-- Local finite type of scheme morphisms is local on the source for the fppf precoverage. -/
instance isLocalAtSourceFppf :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.LocallyOfFiniteType :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage := sorry

end AlgebraicGeometry.LocallyOfFiniteType
