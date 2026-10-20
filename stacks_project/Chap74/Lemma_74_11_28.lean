/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Fpqc
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.28: the property `P(f)` given by “`f` is étale” is fpqc local
on the base. -/
@[stacks 042B] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.Etale S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
