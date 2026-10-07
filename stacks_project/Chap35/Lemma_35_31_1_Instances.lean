module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.LocalAtSource

@[expose] public section

universe u

#check
  (AlgebraicGeometry.Etale.isLocalAtSourceEtale :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.Etale :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.etalePrecoverage)
