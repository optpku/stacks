module

public import Mathlib.AlgebraicGeometry.Spec
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing

/-!
# Strict henselization schemes of algebraic spaces

The strict henselization scheme at a geometric point is the spectrum of its étale local ring.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The strict henselization of an algebraic space at a geometric point is the spectrum of
the étale local ring at that geometric point. -/
noncomputable def strictHenselizationScheme {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) : Scheme.{u} :=
  Spec (etaleLocalRing.asCommRing X xbar)

end AlgebraicGeometry.AlgebraicSpace
