module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Locality

@[expose] public section

universe u

#check
  (AlgebraicGeometry.Flat.isLocalAtSourceFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.Flat :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
