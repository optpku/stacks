module

public import Mathlib.RingTheory.LocalRing.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing

/-!
# Locality of étale local rings

The étale local ring of an algebraic space at a geometric point is a local ring.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The étale local ring of an algebraic space at a geometric point is a local ring. -/
instance etaleLocalRing.instIsLocalRingAtGeometricPoint {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) : IsLocalRing (etaleLocalRing X xbar) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
