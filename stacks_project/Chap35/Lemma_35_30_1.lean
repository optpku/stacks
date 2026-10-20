/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.LocalAtSource
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.30.1: smoothness of scheme morphisms is local on the source for the
smooth precoverage. -/
@[stacks 036U] #check
  (AlgebraicGeometry.Smooth.isLocalAtSourceSmooth :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.Smooth :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSmoothPrecoverage)
