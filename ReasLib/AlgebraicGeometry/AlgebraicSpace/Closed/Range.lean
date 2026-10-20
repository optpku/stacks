module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed
public import Mathlib.Topology.Maps.Basic

/-!
# Closed images of algebraic spaces

A closed morphism of algebraic spaces has closed image on the canonical point
spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Closed

/-- A closed morphism of algebraic spaces has closed image in the canonical
topology on points. -/
theorem isClosed_range_points {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Closed f] : IsClosed (Set.range (Points.map f)) :=
  IsClosedMap.isClosed_range (show IsClosedMap (Points.map f) from Closed.isClosedMap)

end AlgebraicGeometry.AlgebraicSpace.Closed
