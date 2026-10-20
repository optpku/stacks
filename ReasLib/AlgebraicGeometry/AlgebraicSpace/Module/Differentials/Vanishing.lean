module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials

@[expose] public section

open CategoryTheory AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The sheaf of relative differentials `Ω_{X/Y}` of an immersion of algebraic spaces
`f : X ⟶ Y` is zero. -/
theorem isZero_relativeDifferentials_of_isImmersion {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsImmersion f] :
    IsZero (relativeDifferentials f) :=
  sorry

/-- The sheaf of relative differentials of a monomorphism of algebraic spaces vanishes. -/
theorem isZero_relativeDifferentials_of_mono {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Mono f] :
    IsZero (relativeDifferentials f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
