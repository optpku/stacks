module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Affine

@[expose] public section

universe u

#check
  (AlgebraicGeometry.IsAffineHom.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsAffineHom :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
