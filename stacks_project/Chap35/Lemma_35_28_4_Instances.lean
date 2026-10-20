module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversallyOpen.Locality

@[expose] public section

universe u

#check
  (AlgebraicGeometry.UniversallyOpen.isLocalAtSourceFppf :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.UniversallyOpen :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage)
