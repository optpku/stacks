module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.LocallyProjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth

/-!
# Relative differentials of formally smooth morphisms of algebraic spaces

The sheaf of relative differentials of a formally smooth morphism of algebraic
spaces is locally projective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormallySmooth

/-- The sheaf of relative differentials of a formally smooth morphism of algebraic
spaces over a scheme is locally projective. -/
instance instIsLocallyProjectiveRelativeDifferentials {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FormallySmooth f] :
    IsLocallyProjective Ω[f] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FormallySmooth
