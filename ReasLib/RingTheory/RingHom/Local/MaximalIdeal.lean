/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Maximal ideals and local ring homomorphisms

This leaf owns the small ring-map API relating maximal-ideal preservation,
locality, and powers of maximal ideals.  It is intentionally independent of
the broader affine-local property API in `RingHom.Local`.
-/

namespace RingHom

/-- A ring homomorphism between local rings maps the source maximal ideal
onto the target maximal ideal. This is stronger than merely being local. -/
@[stacks 07FH "maximal-ideal-preserving local map"]
def MapsMaximalIdeal {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) : Prop :=
  Ideal.map f (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S

/-- A maximal-ideal-preserving homomorphism of local rings is local. -/
theorem MapsMaximalIdeal.isLocalHom
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] {f : R →+* S}
    (hf : f.MapsMaximalIdeal) : IsLocalHom f := sorry

/-- Every homomorphism from an Artinian local ring to a nontrivial ring is
local. The result is named rather than registered globally, to avoid
polluting typeclass search. -/
theorem isLocalHom_of_artinian
    {R S : Type*} [CommRing R] [CommRing S]
    [IsArtinianRing R] [IsLocalRing R] [Nontrivial S]
    (f : R →+* S) : IsLocalHom f := sorry

namespace IsLocalHom

/-- A local homomorphism carries every power of the source maximal ideal into
the corresponding power of the target maximal ideal. -/
theorem pow_maximalIdeal_le_comap
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) [IsLocalHom f] (n : ℕ) :
    IsLocalRing.maximalIdeal R ^ n ≤
      Ideal.comap f (IsLocalRing.maximalIdeal S ^ n) := sorry

end IsLocalHom

end RingHom
