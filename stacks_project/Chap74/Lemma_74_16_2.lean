/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFiniteType.LocalAtSource
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.16.2: the property `P(f)` given by “`f` is locally of finite
type” is fppf local on the source. -/
@[stacks 06EW] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.isLocalAtSourceFppf :
    MorphismProperty.IsLocalAtSource
      (@LocallyOfFiniteType S : MorphismProperty (AlgebraicSpace S))
      (fppfPrecoverage S))
