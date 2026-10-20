module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf

/-!
# Immersions are fppf local on the target

Immersions of algebraic spaces over a scheme `S` satisfy `IsLocalAtTarget`
for the fppf precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsImmersion

/-- Immersions of algebraic spaces are local on the target for the fppf
precoverage. -/
instance isLocalAtTargetFppf {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (@IsImmersion S : MorphismProperty (AlgebraicSpace S))
      (fppfPrecoverage S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsImmersion
