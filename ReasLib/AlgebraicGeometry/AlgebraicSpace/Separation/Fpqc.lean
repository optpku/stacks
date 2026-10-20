module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sites.FpqcPrecoverage

/-!
# Separated and quasi-separated morphisms are fpqc local on the target

Separated and quasi-separated morphisms of algebraic spaces over a scheme `S`
satisfy `IsLocalAtTarget` for the fpqc precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QuasiSeparated

/-- Quasi-separatedness of morphisms of algebraic spaces is local on the target
for the fpqc precoverage. -/
instance isLocalAtTargetFpqc {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (@QuasiSeparated S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QuasiSeparated

namespace AlgebraicGeometry.AlgebraicSpace.Separated

/-- Separatedness of morphisms of algebraic spaces is local on the target for
the fpqc precoverage. -/
instance isLocalAtTargetFpqc {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (@Separated S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Separated
