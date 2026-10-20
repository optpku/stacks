module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiAffine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sites.FpqcPrecoverage

/-!
# Quasi-affine morphisms are fpqc local on the target

Quasi-affine morphisms of algebraic spaces over a scheme satisfy locality on
the target for the fpqc precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QuasiAffine

/-- Quasi-affine morphisms of algebraic spaces are local on the target for the
fpqc precoverage. -/
instance isLocalAtTargetFpqc {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (@QuasiAffine S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QuasiAffine
