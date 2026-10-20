/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Regular Elements and Associated Primes

This leaf owns both the generic regular-element exclusion for associated primes
and the finite-module prime-avoidance criterion over a Noetherian ring.
-/

universe u v

namespace Ideal

section Regular

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- An ideal containing an element that acts regularly on a module is not an associated prime of
that module.  Unlike the converse prime-avoidance direction, this needs neither finite generation
of the module nor finiteness of its associated-prime set. -/
@[stacks 0BHZ "regular elements avoid associated primes"]
theorem not_mem_associatedPrimes_of_mem_isSMulRegular
    {I : Ideal R} {x : R} (hx : x ∈ I) (hx_regular : IsSMulRegular M x) :
    I ∉ associatedPrimes R M := sorry

end Regular

section Finite

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- An ideal contains an element acting regularly on a module when it avoids every associated
prime, provided that the module has only finitely many associated primes. -/
theorem exists_isSMulRegular_iff_not_le_associatedPrimes_of_finite (I : Ideal R)
    (hfinite : (associatedPrimes R M).Finite) :
    (∃ x ∈ I, IsSMulRegular M x) ↔
      ∀ p ∈ associatedPrimes R M, ¬ I ≤ p := by
  constructor
  · rintro ⟨x, hxI, hxRegular⟩ p hp hIp
    have hxUnion : x ∈ ⋃ q ∈ associatedPrimes R M, q :=
      Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hIp hxI⟩⟩
    rw [biUnion_associatedPrimes_eq_compl_regular R M] at hxUnion
    exact hxUnion hxRegular
  · intro hAvoid
    by_contra! hnone
    have hIUnion : (I : Set R) ⊆ ⋃ p ∈ associatedPrimes R M, p := by
      intro x hxI
      rw [biUnion_associatedPrimes_eq_compl_regular R M]
      exact hnone x hxI
    obtain ⟨p, hp, hIp⟩ :=
      (I.subset_union_prime_finite hfinite (f := id) 0 0
        fun _ hq _ _ ↦ hq.isPrime).mp hIUnion
    exact hAvoid p hp hIp

/-- Lemma 10.63.18 (Tag 00LL): an ideal contains an element acting regularly on a finite
module exactly when it is not contained in any associated prime of that module. -/
@[stacks 00LL]
theorem exists_isSMulRegular_iff_not_le_associatedPrimes [Module.Finite R M] (I : Ideal R) :
    (∃ x ∈ I, IsSMulRegular M x) ↔
      ∀ p ∈ associatedPrimes R M, ¬ I ≤ p :=
  exists_isSMulRegular_iff_not_le_associatedPrimes_of_finite I
    (associatedPrimes.finite R M)

end Finite

end Ideal
