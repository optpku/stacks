/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Isomorphisms.Fpqc
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.15: the property `P(f)` given by “`f` is an isomorphism” is fpqc
local on the base. -/
@[stacks 041Y] #check
  (AlgebraicGeometry.AlgebraicSpace.Isomorphisms.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (MorphismProperty.isomorphisms (AlgebraicSpace S))
      (fpqcPrecoverage S))
