module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Flat

@[expose] public section

universe u

#check
  (AlgebraicGeometry.Flat.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Flat :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
