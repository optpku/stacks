module

public import Mathlib.AlgebraicGeometry.Geometrically.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Normal.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyNoetherianFibers
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Normal.FiberCriterion
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Smooth

/-!
# Locality of locally Noetherian normal morphisms

This file records locality properties of normal morphisms with locally Noetherian fibres.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.LocallyNoetherianNormal

/-- Having locally Noetherian fibres and being normal is local on the target for the fppf
precoverage. -/
instance isLocalAtTargetFppf :
    MorphismProperty.IsLocalAtTarget
      ((AlgebraicGeometry.LocallyNoetherianFibers ⊓ @AlgebraicGeometry.Normal) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage := sorry

/-- Having locally Noetherian fibres and being normal is local on the source for the smooth
precoverage. -/
instance isLocalAtSourceSmooth :
    MorphismProperty.IsLocalAtSource
      ((AlgebraicGeometry.LocallyNoetherianFibers ⊓ @AlgebraicGeometry.Normal) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSmoothPrecoverage := sorry

end AlgebraicGeometry.LocallyNoetherianNormal
