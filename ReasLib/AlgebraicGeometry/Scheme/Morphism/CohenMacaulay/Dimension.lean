module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFormula

/-!
# Dimension of Cohen--Macaulay scheme morphisms

This file records the pointwise local-dimension formula for Cohen--Macaulay
morphisms of locally Noetherian schemes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- For a locally finite-type Cohen--Macaulay morphism of locally Noetherian schemes, the local
dimension at a source point is the local dimension at its image plus the local dimension of the
corresponding fiber. -/
theorem CohenMacaulay.topologicalKrullDimAt_eq_image_add_fiberDimensionAt
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [CohenMacaulay f] (x : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (f x) + f.fiberDimensionAt x := sorry

end AlgebraicGeometry
