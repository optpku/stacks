module

public import stacks_project.Chap74.Lemma_74_11_6_Precoverage
public import stacks_project.Chap74.Lemma_74_11_16_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.16: the property `P(f)` given by “`f` is affine” is fpqc local on
the base. -/
@[stacks 041Z] #check
  (AlgebraicSpace.Affine.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.Affine S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
