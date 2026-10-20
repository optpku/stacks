/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.QuasiCompactAndDominant
import StacksCheckRecall

universe u

open CategoryTheory

/- Lemma 35.23.8: the property `P(f)` given by “`f` is quasi-compact and
dominant” is fpqc local on the base. -/
@[stacks 0H8H] #check
  (AlgebraicGeometry.QuasiCompactAndDominant.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      ((@AlgebraicGeometry.QuasiCompact ⊓ @AlgebraicGeometry.IsDominant) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
