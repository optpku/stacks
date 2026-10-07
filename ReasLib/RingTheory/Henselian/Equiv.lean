module

public import Mathlib.RingTheory.Henselian
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Henselian.StrictHenselian

@[expose] public section

/-!
# Ring Equivalences of Henselian Local Rings

The henselian and strictly henselian local-ring properties are intrinsic to the
underlying ring.  This leaf owns their transport along ring equivalences, including
carrier changes across universes.
-/

universe u v

namespace HenselianLocalRing

/-- A ring equivalence transports a henselian local-ring structure to its target, possibly across
universes. -/
@[stacks 04GE "henselian local rings under ring equivalence"]
theorem of_ringEquiv {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [HenselianLocalRing R] (e : R ≃+* S) : HenselianLocalRing S := sorry

/-- Henselian local-ring structure is invariant under ring equivalence. -/
@[stacks 04GE "henselianity and ring equivalence"]
theorem iff_of_ringEquiv {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) : HenselianLocalRing R ↔ HenselianLocalRing S := sorry

end HenselianLocalRing

namespace StrictHenselianLocalRing

/-- A ring equivalence transports a strictly henselian local-ring structure to its target,
possibly across universes. -/
@[stacks 04GK "strictly henselian local rings under ring equivalence"]
theorem of_ringEquiv {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [StrictHenselianLocalRing R] (e : R ≃+* S) : StrictHenselianLocalRing S := sorry

/-- Strict henselian local-ring structure is invariant under ring equivalence. -/
@[stacks 04GK "strict henselianity and ring equivalence"]
theorem iff_of_ringEquiv {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) : StrictHenselianLocalRing R ↔ StrictHenselianLocalRing S := sorry

end StrictHenselianLocalRing
