/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap74.Lemma_74_11_28_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.28: the property `P(f)` given by “`f` is étale” is fpqc local
on the base. -/
@[stacks 042B] #check
  (AlgebraicSpace.Etale.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.Etale S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
