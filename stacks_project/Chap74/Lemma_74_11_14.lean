module

public import stacks_project.Chap74.Lemma_74_11_6_Precoverage
public import stacks_project.Chap74.Lemma_74_11_14_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.14: the property `P(f)` given by “`f` is an open immersion” is
fpqc local on the base. -/
@[stacks 041X] #check
  (AlgebraicSpace.IsOpenImmersion.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.IsOpenImmersion S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
