module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtSource.AffineDescent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Descent

/-!
# Source locality of smooth scheme morphisms

This file records that smoothness of scheme morphisms is local on the source for the smooth
precoverage.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Smooth

/-- Smoothness of scheme morphisms is local on the source for the smooth precoverage. -/
instance isLocalAtSourceSmooth :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.Smooth :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSmoothPrecoverage := sorry

end AlgebraicGeometry.Smooth
