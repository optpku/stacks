module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.LocalAtSource

@[expose] public section

universe u

#check
  (AlgebraicGeometry.Smooth.isLocalAtSourceSmooth :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.Smooth :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSmoothPrecoverage)
