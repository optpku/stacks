module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Smooth

@[expose] public section

universe u

#check
  (AlgebraicGeometry.Smooth.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Smooth :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
