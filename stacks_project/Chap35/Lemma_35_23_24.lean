module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Integral
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.23.24: integral morphisms of schemes are local on the target for the
fpqc precoverage. -/
@[stacks 02L9] #check
  (AlgebraicGeometry.IsIntegralHom.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsIntegralHom :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
