/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.FiniteType
import StacksCheckRecall

universe u

/- Lemma 35.23.14: the property `P(f)` given by “`f` is of finite type” is fpqc
local on the base. -/
@[stacks 02KZ] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Scheme.Hom.FiniteType :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
