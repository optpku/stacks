module

public import stacks_project.Chap74.Lemma_74_11_6_Precoverage
public import stacks_project.Chap74.Lemma_74_11_18_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.18: the property `P(f)` given by “`f` is separated” is fpqc local
on the base. -/
@[stacks 0421] #check
  (AlgebraicSpace.Separated.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.Separated S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
