/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalAtTarget.FinitePresentation
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.12: the property `P(f)` given by “`f` is of finite presentation”
is fpqc local on the base. -/
@[stacks 041V] #check
  (AlgebraicGeometry.AlgebraicSpace.FinitePresentation.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.FinitePresentation S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
