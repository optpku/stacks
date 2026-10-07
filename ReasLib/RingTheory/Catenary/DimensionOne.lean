module

public import ReasLib.RingTheory.CohenMacaulay.Catenary

/-!
# Universal catenarity in dimension one

This module records universal catenarity for one-dimensional Noetherian domains.
-/

@[expose] public section

universe u v

namespace UniversallyCatenaryRing

/-- A one-dimensional Noetherian domain is universally catenary. -/
theorem of_isDomain_ringKrullDim_eq_one {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (hdim : ringKrullDim R = 1) :
    UniversallyCatenaryRing.{u, v} R := sorry

end UniversallyCatenaryRing
