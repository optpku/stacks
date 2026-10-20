/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.DimensionOne
import StacksCheckRecall

@[expose] public section

universe u

open IsLocalRing

/- Exercise 111.28.2: in a one-dimensional Noetherian local ring, a nonzerodivisor
in the maximal ideal gives a principal quotient of Krull dimension zero, hence an
Artinian quotient and a singleton system of parameters, and the ring has no embedded
prime. Conversely, absence of embedded primes implies existence of a nonzerodivisor
in the maximal ideal. -/
@[stacks 02EG]
#check (IsLocalRing.ringKrullDim_quotient_span_singleton_eq_zero_of_mem_nonZeroDivisors :
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1) {x : R} (hx : x ∈ nonZeroDivisors R)
    (hxm : x ∈ maximalIdeal R),
    ringKrullDim (R ⧸ Ideal.span {x}) = 0)

#check (IsLocalRing.isArtinianRing_quotient_span_singleton_of_mem_nonZeroDivisors :
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1) {x : R} (hx : x ∈ nonZeroDivisors R)
    (hxm : x ∈ maximalIdeal R),
    IsArtinianRing (R ⧸ Ideal.span {x}))

#check (IsLocalRing.isSystemOfParameters_singleton_of_mem_nonZeroDivisors :
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1) {x : R} (hx : x ∈ nonZeroDivisors R)
    (hxm : x ∈ maximalIdeal R),
    IsLocalRing.IsSystemOfParameters (fun _ : Fin 1 ↦ ⟨x, hxm⟩))

#check (IsLocalRing.isSystemOfParameters_singleton_iff_ringKrullDim_quotient_eq_zero :
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1) {x : R} (hxm : x ∈ maximalIdeal R),
    IsLocalRing.IsSystemOfParameters (fun _ : Fin 1 ↦ ⟨x, hxm⟩) ↔
      ringKrullDim (R ⧸ Ideal.span {x}) = 0)

@[stacks 02EG]
#check (IsLocalRing.embeddedPrimes_eq_empty_of_mem_nonZeroDivisors :
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1) {x : R} (hx : x ∈ nonZeroDivisors R)
    (hxm : x ∈ maximalIdeal R),
    embeddedPrimes R = ∅)

@[stacks 02EG]
#check (IsLocalRing.exists_mem_maximalIdeal_mem_nonZeroDivisors_of_embeddedPrimes_eq_empty :
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1) (hembedded : embeddedPrimes R = ∅),
    ∃ x ∈ maximalIdeal R, x ∈ nonZeroDivisors R)

#check (IsLocalRing.exists_mem_maximalIdeal_mem_nonZeroDivisors_iff_embeddedPrimes_eq_empty :
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1),
    (∃ x ∈ maximalIdeal R, x ∈ nonZeroDivisors R) ↔ embeddedPrimes R = ∅)
