/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.DimensionOne
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 33.39.1 Canonical API

The one-dimensional local-ring API is owned by `IsLocalRing.DimensionOne` in
the shared library. This chapter entry records those direct owners without
introducing historical facade names.
-/

universe u

/- Lemma 33.39.1 (1)–(2): the maximal-radical and minimal-prime-avoidance criteria. -/
@[stacks 0C3R] #check
  (IsLocalRing.DimensionOne.maximalIdeal_radical_span_singleton_iff_not_mem_minimalPrimes :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      (hdim : ringKrullDim R = 1) {f : R}
      (hf_mem : f ∈ IsLocalRing.maximalIdeal R),
      IsLocalRing.maximalIdeal R = (Ideal.span ({f} : Set R)).radical ↔
        ∀ p : minimalPrimes R, f ∉ p.1)

/- Lemma 33.39.1 (2)–(3): minimal-prime avoidance and the localization product. -/
@[stacks 0C3R] #check
  (IsLocalRing.DimensionOne.away_equiv_pi_minimalPrimeLocalizations_iff_not_mem_minimalPrimes :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      (hdim : ringKrullDim R = 1) {f : R}
      (hf_mem : f ∈ IsLocalRing.maximalIdeal R),
      Nonempty
          (Localization.Away f ≃ₐ[R]
            ((p : minimalPrimes R) → Localization.AtPrime p.1)) ↔
        ∀ p : minimalPrimes R, f ∉ p.1)

/- Lemma 33.39.1, existence: a parameter in the maximal ideal with maximal radical. -/
@[stacks 0C3R] #check
  (IsLocalRing.DimensionOne.exists_mem_maximalIdeal_radical_span_singleton :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      (hdim : ringKrullDim R = 1),
      ∃ f : R, f ∈ IsLocalRing.maximalIdeal R ∧
        IsLocalRing.maximalIdeal R = (Ideal.span ({f} : Set R)).radical)

/- Lemma 33.39.1 (4)–(2): the depth-one nonzerodivisor criterion. -/
@[stacks 0C3R] #check
  (IsLocalRing.DimensionOne.mem_nonZeroDivisors_iff_not_mem_minimalPrimes_of_moduleDepth_eq_one :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      (hdim : ringKrullDim R = 1) (hdepth : moduleDepth R R = 1)
      {f : R} (hf_mem : f ∈ IsLocalRing.maximalIdeal R),
      f ∈ nonZeroDivisors R ↔ ∀ p : minimalPrimes R, f ∉ p.1)

/- Lemma 33.39.1 (5)–(4): the total-fraction localization criterion. -/
@[stacks 0C3R] #check
  (IsLocalRing.DimensionOne.away_isFractionRing_iff_mem_nonZeroDivisors_of_moduleDepth_eq_one :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      (hdim : ringKrullDim R = 1) (hdepth : moduleDepth R R = 1)
      {f : R} (hf_mem : f ∈ IsLocalRing.maximalIdeal R),
      IsFractionRing R (Localization.Away f) ↔ f ∈ nonZeroDivisors R)

/- Lemma 33.39.1, reduced depth: reducedness implies self-module depth one. -/
@[stacks 0C3R] #check
  (IsLocalRing.DimensionOne.self_moduleDepth_eq_one_of_isReduced :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      (hdim : ringKrullDim R = 1) [IsReduced R],
      moduleDepth R R = 1)

/- Lemma 33.39.1 (6)–(3): the reduced residue-field and localization products. -/
@[stacks 0C3R] #check
  (IsLocalRing.DimensionOne.away_equiv_pi_minimalPrimeResidueFields_iff :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      (hdim : ringKrullDim R = 1) [IsReduced R]
      {f : R} (hf_mem : f ∈ IsLocalRing.maximalIdeal R),
      Nonempty
          (Localization.Away f ≃ₐ[R]
            ((p : minimalPrimes R) → p.1.ResidueField)) ↔
        Nonempty
          (Localization.Away f ≃ₐ[R]
            ((p : minimalPrimes R) → Localization.AtPrime p.1)))
