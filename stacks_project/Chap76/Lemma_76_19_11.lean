module

public import stacks_project.Chap76.Lemma_76_19_11_LocalAtTarget
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 76.19.11: the property `P(f)` given by “`f` is formally smooth” is
fpqc local on the base. -/
@[stacks 06CS] #check
  (AlgebraicSpace.FormallySmooth.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.FormallySmooth S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
