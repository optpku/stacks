/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtSource.AffineDescent

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- Injectivity on stalks is local on the source for the fpqc precoverage. -/
instance stalkwiseInjective_isLocalAtSourceFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (stalkwise (Function.Injective ·) :
        CategoryTheory.MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry
