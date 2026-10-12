/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap74.Lemma_74_11_30_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.30: the property `P(f)` given by “`f` is a monomorphism” is fpqc
local on the base. -/
@[stacks 042D] #check
  (AlgebraicSpace.Monomorphisms.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (MorphismProperty.monomorphisms (AlgebraicSpace S))
      (fpqcPrecoverage S))
