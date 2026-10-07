module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Open.Locality

@[expose] public section

universe u

namespace AlgebraicGeometry.UniversallyOpen

/-- Universal openness of scheme morphisms is local on the source for the fppf
precoverage. -/
instance isLocalAtSourceFppf :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.UniversallyOpen :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage := sorry

end AlgebraicGeometry.UniversallyOpen
