module

public import Mathlib.Topology.Spectral.Prespectral
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology

/-!
# Compact open neighbourhoods of algebraic-stack points

Compact open subsets form a basis of the canonical topology on algebraic-stack points.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Compact open subsets form a basis of the canonical topology on the points of an
algebraic stack. -/
instance instPrespectralSpacePoints {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : PrespectralSpace (Points X) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
