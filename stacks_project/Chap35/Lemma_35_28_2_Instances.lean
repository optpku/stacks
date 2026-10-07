module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Locality

@[expose] public section

universe u

#check
  (AlgebraicGeometry.LocallyOfFiniteType.isLocalAtSourceFppf :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.LocallyOfFiniteType :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage)
