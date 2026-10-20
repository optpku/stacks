module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.IndQuasiAffine
import StacksCheckRecall

universe u

/- Lemma 37.66.7: The property of being ind-quasi-affine is fpqc local on the
base. -/
@[stacks 0AP8] #check
  (AlgebraicGeometry.IndQuasiAffineHom.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IndQuasiAffineHom :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
