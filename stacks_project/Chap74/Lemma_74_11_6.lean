/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap74.Lemma_74_11_6_Precoverage
public import stacks_project.Chap74.Lemma_74_11_6_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.6: the property `P(f)` given by “`f` is surjective” is fpqc local
on the base. -/
@[stacks 041Q] #check
  (Surjective.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@Surjective S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
