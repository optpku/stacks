module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat.Fpqc
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.13: the property `P(f)` given by “`f` is flat” is fpqc local on
the base. -/
@[stacks 041W] #check
  (AlgebraicGeometry.AlgebraicSpace.Flat.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.Flat S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
