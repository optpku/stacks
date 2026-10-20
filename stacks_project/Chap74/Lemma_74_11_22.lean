/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Integral.Fpqc
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.22: the property `P(f)` given by “`f` is integral” is fpqc local
on the base. -/
@[stacks 0425] #check
  (AlgebraicGeometry.AlgebraicSpace.IsIntegralHom.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.IsIntegralHom S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
