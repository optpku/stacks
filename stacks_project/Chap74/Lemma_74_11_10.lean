module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation.Fpqc
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.10: the property `P(f)` given by “`f` is locally of finite
presentation” is fpqc local on the base. -/
@[stacks 041T] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
