module

public import ReasLib.Data.Set.Card
public import ReasLib.RingTheory.Ideal.MinimalPrime.Flat
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cardinalities of minimal primes under injective maps

Contraction along an injective ring map covers every minimal prime of the source. This file
records the resulting cardinality and finiteness consequences independently of any particular
faithfully flat or Henselian construction.
-/

@[expose] public section

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- An injective ring map cannot decrease the number of minimal primes. -/
@[stacks 0CB3 "minimal-prime cardinality under injective maps"]
theorem encard_minimalPrimes_le_of_injective
    (hf : Function.Injective f) :
    (minimalPrimes R).encard ≤ (minimalPrimes S).encard := by
  obtain ⟨t, ht, hbij⟩ := (surjOn_minimalPrimes_of_injective hf).exists_bijOn_subset
  calc
    (minimalPrimes R).encard = (Ideal.comap f '' t).encard :=
      congrArg Set.encard hbij.image_eq.symm
    _ = t.encard := hbij.injOn.encard_image
    _ ≤ (minimalPrimes S).encard := Set.encard_le_encard ht

/-- If the target of an injective ring map has finitely many minimal primes, so does the source. -/
@[stacks 0CB3 "minimal-prime finiteness under injective maps"]
theorem minimalPrimes_finite_of_injective
    (hf : Function.Injective f) (h : (minimalPrimes S).Finite) :
    (minimalPrimes R).Finite := by
  rw [← Set.encard_lt_top_iff] at h ⊢
  exact (encard_minimalPrimes_le_of_injective hf).trans_lt h

/-- If the source of an injective ring map has infinitely many minimal primes, so does the
target. -/
@[stacks 0CB3 "infinitely many minimal primes under injective maps"]
theorem minimalPrimes_infinite_of_injective
    (hf : Function.Injective f) (h : (minimalPrimes R).Infinite) :
    (minimalPrimes S).Infinite := fun hS ↦
  h (minimalPrimes_finite_of_injective hf hS)

end RingHom
