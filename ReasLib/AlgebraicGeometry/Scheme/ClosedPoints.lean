module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.JacobsonSpace

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Every nonempty quasi-compact scheme has a closed point. -/
theorem exists_closedPoint_of_compactSpace (X : Scheme.{u}) [CompactSpace X] [Nonempty X] :
    (closedPoints X).Nonempty := sorry

end AlgebraicGeometry.Scheme
