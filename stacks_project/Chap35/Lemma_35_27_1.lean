/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Locality
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.27.1: flatness of scheme morphisms is local on the source for the
fpqc precoverage. -/
@[stacks 036K] #check
  (AlgebraicGeometry.Flat.isLocalAtSourceFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.Flat :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
