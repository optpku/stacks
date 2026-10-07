module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.Locality

universe u

#check
  (AlgebraicGeometry.PseudoCoherent.isLocalAtSourceFppf :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.PseudoCoherent :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage)
