/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Syntomic
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

/- Lemma 35.23.28: syntomicity of scheme morphisms is local on the target for
the fpqc precoverage. -/
@[stacks 02VK] #check
  (AlgebraicGeometry.Syntomic.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Syntomic : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
