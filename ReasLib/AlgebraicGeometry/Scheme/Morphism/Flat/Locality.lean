/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtSource.AffineDescent

/-!
# Locality of flatness for scheme morphisms

This file records locality properties of flat morphisms of schemes.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Flat

/-- Flatness of scheme morphisms is local on the source for the fpqc precoverage. -/
instance isLocalAtSourceFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.Flat :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.Flat
