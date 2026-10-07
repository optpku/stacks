module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.QuasiCompact
import StacksCheckRecall

universe u

/- Lemma 35.23.1: the property `P(f)` given by “`f` is quasi-compact” is fpqc
local on the base. -/
@[stacks 02KQ] #check
  (AlgebraicGeometry.QuasiCompact.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.QuasiCompact :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
