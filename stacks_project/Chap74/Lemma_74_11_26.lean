module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth.Fpqc
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.26: the property `P(f)` given by “`f` is smooth” is fpqc local
on the base. -/
@[stacks 0429] #check
  (AlgebraicSpace.Smooth.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.Smooth S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
