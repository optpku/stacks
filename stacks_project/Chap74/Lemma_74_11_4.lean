module

public import stacks_project.Chap74.Lemma_74_11_4_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.4: the property `P(f)` given by “`f` is universally open” is
fpqc local on the base. -/
@[stacks 041P] #check
  (AlgebraicSpace.UniversallyOpen.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.UniversallyOpen S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
