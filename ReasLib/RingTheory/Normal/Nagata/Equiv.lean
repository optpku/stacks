module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Nagata

@[expose] public section

/-!
# Equivalences of Japanese Domains

This module records transport of the `N-2` condition across ring equivalences.
-/

universe u v

namespace RingEquiv

/-- A ring equivalence transports the `N-2` condition. -/
theorem isN2Ring {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    (e : R ≃+* S) [IsN2Ring R] : IsN2Ring S := sorry

end RingEquiv
