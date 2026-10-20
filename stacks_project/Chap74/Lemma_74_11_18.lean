module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Fpqc
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.18: the property `P(f)` given by “`f` is separated” is fpqc local
on the base. -/
@[stacks 0421] #check
  (AlgebraicGeometry.AlgebraicSpace.Separated.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.Separated S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
