module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Etale

@[expose] public section

universe u

#check
  (AlgebraicGeometry.Etale.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Etale :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
