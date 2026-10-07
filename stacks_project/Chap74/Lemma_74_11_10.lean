module

public import stacks_project.Chap74.Lemma_74_11_10_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.10: the property `P(f)` given by “`f` is locally of finite
presentation” is fpqc local on the base. -/
@[stacks 041T] #check
  (AlgebraicSpace.LocallyOfFinitePresentation.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
