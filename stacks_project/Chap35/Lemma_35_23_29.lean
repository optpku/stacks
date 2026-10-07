module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Smooth
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.23.29: smoothness of scheme morphisms is local on the target for the
fpqc precoverage. -/
@[stacks 02VL] #check
  (AlgebraicGeometry.Smooth.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Smooth :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
