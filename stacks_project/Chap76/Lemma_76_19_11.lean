module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth.Fpqc
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 76.19.11: the property `P(f)` given by “`f` is formally smooth” is
fpqc local on the base. -/
@[stacks 06CS] #check
  (AlgebraicGeometry.AlgebraicSpace.FormallySmooth.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.FormallySmooth S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
