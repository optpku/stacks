/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Minimal primes under flat ring maps

Flatness is the exact hypothesis needed for contraction to preserve minimal primes. Injectivity is
enough for every minimal prime of the source to lift, while faithful flatness packages both facts.

@stack 00HS
@stack 0CB3
-/

@[expose] public section

universe u v

namespace RingHom.Flat

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- A minimal prime contracts to a minimal prime along a flat ring map. -/
@[stacks 00HS "flat contraction of minimal primes"]
theorem comap_mem_minimalPrimes (hf : f.Flat) {q : Ideal S}
    (hq : q ∈ minimalPrimes S) :
    Ideal.comap f q ∈ minimalPrimes R := sorry

/-- Contraction along a flat ring map sends minimal primes to minimal primes. -/
@[stacks 00HS "flat maps send minimal primes to minimal primes"]
theorem mapsTo_minimalPrimes (hf : f.Flat) :
    Set.MapsTo (Ideal.comap f) (minimalPrimes S) (minimalPrimes R) := sorry

end RingHom.Flat

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- Along an injective ring map, every minimal prime of the source is the contraction of a
minimal prime of the target. -/
@[stacks 0CB3 "minimal-prime lifting along injective ring maps"]
theorem surjOn_minimalPrimes_of_injective (hf : Function.Injective f) :
    Set.SurjOn (Ideal.comap f) (minimalPrimes S) (minimalPrimes R) := sorry

end RingHom

namespace RingHom.FaithfullyFlat

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- Contraction along a faithfully flat ring map sends minimal primes to minimal primes. -/
@[stacks 0CB3 "faithfully flat maps send minimal primes to minimal primes"]
theorem mapsTo_minimalPrimes (hf : f.FaithfullyFlat) :
    Set.MapsTo (Ideal.comap f) (minimalPrimes S) (minimalPrimes R) := sorry

/-- Contraction along a faithfully flat ring map is surjective on minimal primes. -/
@[stacks 0CB3 "faithfully flat surjectivity on minimal primes"]
theorem surjOn_minimalPrimes (hf : f.FaithfullyFlat) :
    Set.SurjOn (Ideal.comap f) (minimalPrimes S) (minimalPrimes R) := sorry

/-- The contractions of the minimal primes along a faithfully flat map are exactly the minimal
primes of the source. -/
@[stacks 0CB3 "image of minimal primes under faithfully flat contraction"]
theorem image_minimalPrimes (hf : f.FaithfullyFlat) :
    Ideal.comap f '' minimalPrimes S = minimalPrimes R := sorry

/-- If the target of a faithfully flat ring map has a unique minimal prime, then so does its
source. -/
@[stacks 0BQ0 "faithfully flat descent of a unique minimal prime"]
theorem uniqueMinimalPrime_of_target (hf : f.FaithfullyFlat)
    (h : ∃! q : Ideal S, q ∈ minimalPrimes S) :
    ∃! p : Ideal R, p ∈ minimalPrimes R := sorry

end RingHom.FaithfullyFlat
