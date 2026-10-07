module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.QuasiSeparated
import StacksCheckRecall

universe u

/- Lemma 35.23.2: the property `P(f)` given by “`f` is quasi-separated” is fpqc
local on the base. -/
@[stacks 02KR] #check
  (AlgebraicGeometry.QuasiSeparated.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.QuasiSeparated :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
