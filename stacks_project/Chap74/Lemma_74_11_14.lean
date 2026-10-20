/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenImmersion.Fpqc
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.14: the property `P(f)` given by “`f` is an open immersion” is
fpqc local on the base. -/
@[stacks 041X] #check
  (AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (fun {_ _} f ↦ AlgebraicSpace.IsOpenImmersion f : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
