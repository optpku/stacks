module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RestrictedPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Coproduct

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforwardCohomologyIn

/-- Derived pushforward along a quasi-compact and quasi-separated morphism of algebraic
spaces preserves coproducts indexed by types in the scheme universe. -/
instance preservesCoproducts {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (pushforwardCohomologyIn f) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforwardCohomologyIn
