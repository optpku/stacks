module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Coproduct
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.CohomologicalDimension

/-!
# Coproducts and derived pushforward

This module records preservation of coproducts by derived pushforward on complexes with
quasicoherent cohomology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn

/-- Derived pushforward along a quasi-compact and quasi-separated morphism preserves
coproducts indexed by types in the scheme universe. -/
instance preservesCoproducts {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (pushforwardCohomologyIn f) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn
