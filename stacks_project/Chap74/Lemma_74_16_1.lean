/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation.LocalAtSource
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.16.1: the property `P(f)` given by “`f` is locally of finite
presentation” is fppf local on the source. -/
@[stacks 06EV] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation.isLocalAtSourceFppf :
    MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S))
      (AlgebraicGeometry.AlgebraicSpace.fppfPrecoverage S))
