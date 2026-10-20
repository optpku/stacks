module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf

/-!
# Fppf locality of locally separated morphisms

Local separatedness of morphisms of algebraic spaces over a scheme is local on
the target for the fppf precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.LocallySeparated

/-- Locally separated morphisms of algebraic spaces are local on the target for
the fppf precoverage. -/
instance isLocalAtTargetFppf {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (@LocallySeparated S : MorphismProperty (AlgebraicSpace S))
      (fppfPrecoverage S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.LocallySeparated
