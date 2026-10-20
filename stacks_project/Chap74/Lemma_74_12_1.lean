module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.Fppf
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.12.1: the property `P(f)` given by “`f` is an immersion” is fppf
local on the base. -/
@[stacks 042U] #check
  (AlgebraicGeometry.AlgebraicSpace.IsImmersion.isLocalAtTargetFppf :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.IsImmersion S : MorphismProperty (AlgebraicSpace S))
      (fppfPrecoverage S))
