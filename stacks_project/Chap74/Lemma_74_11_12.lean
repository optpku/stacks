module

public import stacks_project.Chap74.Lemma_74_11_12_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.12: the property `P(f)` given by “`f` is of finite presentation”
is fpqc local on the base. -/
@[stacks 041V] #check
  (AlgebraicSpace.FinitePresentation.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.FinitePresentation S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
