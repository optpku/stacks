module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.QuasiCompactImmersion
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.23.23: the property of being a quasi-compact immersion is fpqc
local on the base. -/
@[stacks 02L8] #check
  (AlgebraicGeometry.QuasiCompactImmersion.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      ((@AlgebraicGeometry.QuasiCompact ⊓ @AlgebraicGeometry.IsImmersion) :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
