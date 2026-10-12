/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap74.Lemma_74_11_6_Precoverage
public import stacks_project.Chap74.Lemma_74_11_17_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.17: the property `P(f)` given by “`f` is a closed immersion” is
fpqc local on the base. -/
@[stacks 0420] #check
  (AlgebraicSpace.IsClosedImmersion.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.IsClosedImmersion S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
