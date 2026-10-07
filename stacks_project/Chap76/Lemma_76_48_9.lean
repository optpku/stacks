module

public import stacks_project.Chap76.Lemma_76_48_9_LocalAtTarget
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 76.48.9: the property `P(f)` given by “`f` is a local complete
intersection morphism” is fpqc local on the base. -/
@[stacks 0CHM] #check
  (IsLocalCompleteIntersection.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@IsLocalCompleteIntersection S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
