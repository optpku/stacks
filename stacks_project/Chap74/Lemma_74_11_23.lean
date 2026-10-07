module

public import stacks_project.Chap74.Lemma_74_11_23_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.23: the property `P(f)` given by “`f` is finite” is fpqc local
on the base. -/
@[stacks 0426] #check
  (AlgebraicSpace.IsFinite.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.IsFinite S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
