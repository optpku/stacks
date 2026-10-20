/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein.Syntomic

@[expose] public section

universe u

/- Compatibility check for the promoted syntomic-locality instance. -/
#check
  (AlgebraicGeometry.Scheme.Gorenstein.isLocalSyntomic :
    CategoryTheory.ObjectProperty.IsLocal
      (AlgebraicGeometry.Scheme.Gorenstein :
        CategoryTheory.ObjectProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSyntomicPrecoverage)
