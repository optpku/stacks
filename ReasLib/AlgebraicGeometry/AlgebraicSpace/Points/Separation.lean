module

public import Mathlib.Topology.Separation.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Separation of algebraic-space point spaces

The canonical point space of a decent algebraic space is Kolmogorov.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical point space of a decent algebraic space over a scheme is Kolmogorov. -/
instance instT0SpacePoints {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] :
    T0Space (Points X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
