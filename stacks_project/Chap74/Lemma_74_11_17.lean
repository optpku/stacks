module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Fpqc
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.17: the property `P(f)` given by “`f` is a closed immersion” is
fpqc local on the base. -/
@[stacks 0420] #check
  (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.IsClosedImmersion S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
