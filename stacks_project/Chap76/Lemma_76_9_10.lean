/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.Fpqc
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 76.9.10 (1): being a thickening is local on the target for the fpqc precoverage. -/
@[stacks 0BPI] #check
  (AlgebraicGeometry.AlgebraicSpace.IsThickening.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@IsThickening S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))

/- Lemma 76.9.10 (2): being a first-order thickening is local on the target for the fpqc
precoverage. -/
@[stacks 0BPI] #check
  (AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@IsFirstOrderThickening S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
