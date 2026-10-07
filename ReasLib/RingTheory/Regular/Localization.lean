module

public import Mathlib.Data.List.TFAE
public import ReasLib.RingTheory.Flat.Localization.AtPrime
public import ReasLib.RingTheory.Regular.RingMap
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Local criteria for regular ring maps

@stack 07C0

The predicates in this module keep the canonical localized homomorphism on the
public surface and do not register localization algebra structures globally.
-/

namespace RingHom.Regular

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring map is regular at every prime of its target. -/
@[stacks 07C0 "regular at target primes"]
def AtPrimes (f : R →+* S) : Prop :=
  ∀ q : PrimeSpectrum S,
    (Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl).Regular

/-- A ring map is regular at the relevant maximal ideals of its target. -/
@[stacks 07C0 "regular at target maximal ideals"]
def AtMaximals (f : R →+* S) : Prop :=
  ∀ m : MaximalSpectrum S, Ideal.IsMaximal (m.asIdeal.comap f) →
    (Localization.localRingHom (m.asIdeal.comap f) m.asIdeal f rfl).Regular

variable {f : R →+* S}

/-- Regularity is preserved after localizing at a target prime. -/
@[stacks 07C0 "regularity after localization at a target prime"]
theorem localizeAtPrime (h : f.Regular) (q : PrimeSpectrum S) :
    (Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl).Regular := sorry

variable [IsNoetherianRing S]

/-- For a Noetherian target, regularity is detected at target primes. -/
@[stacks 07C0 "regularity is local at target primes"]
theorem iff_atPrimes : f.Regular ↔ AtPrimes f := sorry

/-- For a Noetherian target, regularity is detected at the relevant maximal ideals. -/
@[stacks 07C0 "regularity is local at target maximal ideals"]
theorem iff_atMaximals : f.Regular ↔ AtMaximals f := sorry

/-- Lemma 15.41.2: the global, prime-local, and maximal-local regularity conditions agree. -/
@[stacks 07C0 "regular ring maps are local"]
theorem local_tfae :
    ([f.Regular, AtPrimes f, AtMaximals f] : List Prop).TFAE := sorry

end RingHom.Regular
