module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RestrictedPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.Permanence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Permanence

/-!
# Right adjoint of derived pushforward on algebraic spaces

Restricted derived pushforward on `DerivedQCoh` along a morphism of
quasi-compact quasi-separated algebraic spaces is a left adjoint.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Derived pushforward on `DerivedQCoh` along a morphism of quasi-compact
quasi-separated algebraic spaces has a right adjoint. -/
instance pushforwardIsLeftAdjoint {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y] :
    (pushforwardCohomologyIn f).IsLeftAdjoint :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
