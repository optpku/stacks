module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictHenselization
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing

/-!
# Strict henselization of an algebraic space at a geometric point

The strict henselization of an algebraic space at a geometric point is the spectrum of
the étale local ring at that geometric point.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The strict henselization scheme is definitionally the spectrum of the étale local
ring. -/
theorem strictHenselizationScheme_def {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) :
    strictHenselizationScheme xbar =
      Spec (etaleLocalRing.asCommRing X xbar) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
