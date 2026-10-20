/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism.Fpqc
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.8: the property `P(f)` given by “`f` is a universal homeomorphism”
is fpqc local on the base. -/
@[stacks 0CFX] #check
  (AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.UniversalHomeomorphism S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
