module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.MinimalModel

@[expose] public section

open scoped AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom (IsMinimalModel)

universe u

namespace AlgebraicGeometry.ProjectiveLine

/-- The projective line over a discrete valuation ring is a minimal model. -/
instance isMinimalModel (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] :
    IsMinimalModel (ProjectiveSpace.toSpec R 1) := sorry

end AlgebraicGeometry.ProjectiveLine
