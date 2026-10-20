/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.QuasiAffine
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.23.22: quasi-affineness of scheme morphisms is local on the target
for the fpqc precoverage. -/
@[stacks 02L7] #check
  (AlgebraicGeometry.QuasiAffineHom.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.QuasiAffineHom :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
