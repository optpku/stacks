module

public import stacks_project.Chap74.Lemma_74_11_6_Precoverage
public import stacks_project.Chap74.Lemma_74_11_19_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.19: the property `P(f)` given by “`f` is proper” is fpqc local
on the base. -/
@[stacks 0422] #check
  (AlgebraicSpace.Proper.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.Proper S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
