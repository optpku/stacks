module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyInjective.Fpqc
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.7: the property `P(f)` given by “`f` is universally injective” is
fpqc local on the base. -/
@[stacks 041R] #check
  (AlgebraicGeometry.AlgebraicSpace.UniversallyInjective.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.UniversallyInjective S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
