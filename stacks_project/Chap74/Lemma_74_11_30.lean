module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Monomorphism.Fpqc
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.30: the property `P(f)` given by “`f` is a monomorphism” is fpqc
local on the base. -/
@[stacks 042D] #check
  (AlgebraicGeometry.AlgebraicSpace.Monomorphisms.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (MorphismProperty.monomorphisms (AlgebraicSpace S))
      (fpqcPrecoverage S))
