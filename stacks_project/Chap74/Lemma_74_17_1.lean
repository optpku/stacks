/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic.LocalAtSource
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.17.1: the property `P(f)` given by “`f` is syntomic” is syntomic
local on the source. -/
@[stacks 06F0] #check
  (AlgebraicGeometry.AlgebraicSpace.Syntomic.isLocalAtSourceSyntomic :
    MorphismProperty.IsLocalAtSource
      (@Syntomic S : MorphismProperty (AlgebraicSpace S))
      (precoverage (@Syntomic S)))
