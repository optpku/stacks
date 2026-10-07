module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.UniversalHomeomorphism
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.23.11: the property `P(f)` given by “`f` is a universal
homeomorphism” is fpqc local on the base. -/
@[stacks 0CEX] #check
  (AlgebraicGeometry.UniversalHomeomorphism.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.UniversalHomeomorphism :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
