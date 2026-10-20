/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.IndQuasiAffine
import StacksCheckRecall

universe u

/- Lemma 37.66.7: The property of being ind-quasi-affine is fpqc local on the
base. -/
@[stacks 0AP8] #check
  (AlgebraicGeometry.IndQuasiAffineHom.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IndQuasiAffineHom :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
