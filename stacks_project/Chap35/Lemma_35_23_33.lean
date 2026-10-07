module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Monomorphism
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

/- Lemma 35.23.33: the property that a scheme morphism is a monomorphism is fpqc
local on the base. -/
@[stacks 02YK] #check
  (AlgebraicGeometry.Monomorphisms.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (MorphismProperty.monomorphisms AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
