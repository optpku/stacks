module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sites.FpqcPrecoverage

/-!
# Closed immersions are fpqc local on the target

Closed immersions of algebraic spaces over a scheme `S` satisfy `IsLocalAtTarget`
for the fpqc precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion

/-- Closed immersions of algebraic spaces are local on the target for the fpqc
precoverage. -/
instance isLocalAtTargetFpqc {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (@IsClosedImmersion S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion
