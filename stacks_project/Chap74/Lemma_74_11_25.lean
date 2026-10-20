module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalAtTarget.Syntomic
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.25: the property `P(f)` given by “`f` is syntomic” is fpqc local
on the base. -/
@[stacks 0428] #check
  (AlgebraicGeometry.AlgebraicSpace.Syntomic.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.Syntomic S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
