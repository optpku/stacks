/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_9_10_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 76.9.10 (1): being a thickening is local on the target for the fpqc precoverage. -/
@[stacks 0BPI] #check
  (IsThickening.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@IsThickening S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))

/- Lemma 76.9.10 (2): being a first-order thickening is local on the target for the fpqc
precoverage. -/
@[stacks 0BPI] #check
  (IsFirstOrderThickening.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@IsFirstOrderThickening S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
