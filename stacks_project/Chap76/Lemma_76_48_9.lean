module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalAtTarget.LocalCompleteIntersection
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 76.48.9: the property `P(f)` given by “`f` is a local complete
intersection morphism” is fpqc local on the base. -/
@[stacks 0CHM] #check
  (AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@IsLocalCompleteIntersection S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
