/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Etale.LocalAtSource
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.19.1: the property `P(f)` given by “`f` is étale” is étale
local on the source. -/
@[stacks 06F4] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.isLocalAtSourceEtale :
    MorphismProperty.IsLocalAtSource
      (@AlgebraicSpace.Etale S : MorphismProperty (AlgebraicSpace S))
      (etalePrecoverage (S := S)))
