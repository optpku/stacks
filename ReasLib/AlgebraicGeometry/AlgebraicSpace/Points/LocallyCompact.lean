module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Compact open neighbourhoods of algebraic-space points

Compact open subsets form a basis of the canonical topology on algebraic-space points.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Points

/-- Compact open subsets form a basis of the canonical topology on the points of an
algebraic space. -/
instance prespectralSpace {S : Scheme.{u}} (X : AlgebraicSpace S) :
    PrespectralSpace (Points X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Points
