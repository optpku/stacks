module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.DeligneMumford
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiSeparated

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.DeligneMumfordStack

open AlgebraicStack

/-- The dimension at a point of a quasi-separated locally Noetherian Deligne–Mumford
stack equals the local topological Krull dimension of its space of points. -/
theorem dimensionAt_eq_topologicalKrullDimAt {S : Scheme.{u}} {X : GroupoidsOver S}
    [DeligneMumfordStack X] [AlgebraicStack.IsLocallyNoetherian X]
    [IsQuasiSeparated X] (x : Points X) :
    dimensionAt x = dimensionToEInt (topologicalKrullDimAt x) :=
  sorry

end AlgebraicGeometry.DeligneMumfordStack
