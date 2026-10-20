module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent

/-!
# Dimension of decent algebraic spaces

On a decent algebraic space, étale-local dimension agrees with the topological
Krull dimension of the space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The dimension at a point of a decent algebraic space equals the local
topological Krull dimension of its space of points. -/
theorem dimensionAt_eq_topologicalKrullDimAt_of_isDecent {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (x : Points X) :
    dimensionAt x = topologicalKrullDimAt x :=
  sorry

/-- The dimension of a decent algebraic space equals the topological Krull
dimension of its space of points. -/
theorem dimension_eq_topologicalKrullDim_of_isDecent {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] :
    dimension X = topologicalKrullDim (Points X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
