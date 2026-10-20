/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.Fpqc
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.9: the property `P(f)` given by “`f` is locally of finite type”
is fpqc local on the base. -/
@[stacks 041S] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.LocallyOfFiniteType S :
        MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
