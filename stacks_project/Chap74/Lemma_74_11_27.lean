module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.Fpqc
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.27: the property `P(f)` given by “`f` is unramified” is fpqc local
on the base. -/
@[stacks 042A] #check
  (AlgebraicSpace.Unramified.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.Unramified S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
