/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyOpen.LocalAtSource
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.16.4: the property `P(f)` given by “`f` is universally open” is fppf
local on the source. -/
@[stacks 06EY] #check
  (AlgebraicGeometry.AlgebraicSpace.UniversallyOpen.isLocalAtSourceFppf :
    MorphismProperty.IsLocalAtSource
      (@UniversallyOpen S : MorphismProperty (AlgebraicSpace S))
      (fppfPrecoverage S))
