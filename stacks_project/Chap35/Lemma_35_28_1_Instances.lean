module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Locality

@[expose] public section

universe u

#check
  (AlgebraicGeometry.LocallyOfFinitePresentation.isLocalAtSourceFppf :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.LocallyOfFinitePresentation :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage)
