/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Open.Locality

@[expose] public section

universe u

#check (AlgebraicGeometry.isOpenMap_isLocalAtSourceFppf :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (AlgebraicGeometry.topologically (@IsOpenMap) :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage)
