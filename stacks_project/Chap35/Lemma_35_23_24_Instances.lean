module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Integral

@[expose] public section

universe u

#check
  (AlgebraicGeometry.IsIntegralHom.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsIntegralHom :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
