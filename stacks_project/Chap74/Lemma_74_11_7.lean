/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap74.Lemma_74_11_7_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.7: the property `P(f)` given by “`f` is universally injective” is
fpqc local on the base. -/
@[stacks 041R] #check
  (AlgebraicSpace.UniversallyInjective.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.UniversallyInjective S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
