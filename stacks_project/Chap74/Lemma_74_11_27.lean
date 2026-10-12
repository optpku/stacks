/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap74.Lemma_74_11_27_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.27: the property `P(f)` given by “`f` is unramified” is fpqc local
on the base. -/
@[stacks 042A] #check
  (AlgebraicSpace.Unramified.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.Unramified S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
