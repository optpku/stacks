/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Operations
public import ReasLib.RingTheory.Spectrum.Prime.Localization.Homeomorph
import StacksCheckRecall

@[expose] public section

/-!
@stack 02LX

# The total quotient ring from the minimal-prime localizations

The chapter keeps the concrete product equivalence from the source. Spectrum
and localization transport used to construct it are recalled from their owners.
-/

universe u

noncomputable section

variable (R : Type u) [CommRing R]

-- Local declaration justification (source-local instance): `minimalPrimes R` stores primality as
-- subtype data, while `Localization.AtPrime p.1` requests the same fact through typeclass search.
local instance (p : minimalPrimes R) : p.1.IsPrime :=
  p.2.isPrime

variable [Finite (minimalPrimes R)]

/-- Lemma 10.25.4: if the finitely many minimal primes of `R` cover exactly the zero divisors,
then the total quotient ring is canonically equivalent to the product of the corresponding local
rings. -/
@[stacks 02LX]
noncomputable def fractionRing_equiv_pi_minimalPrimeLocalizations
    (hzdiv :
      (⋃ p : minimalPrimes R, (p.1 : Set R)) =
        {x : R | x ∉ nonZeroDivisors R}) :
    FractionRing R ≃ₐ[R] ∀ p : minimalPrimes R, Localization.AtPrime p.1 := sorry

/-- The total-quotient-ring equivalence commutes with the canonical map from `R`. -/
@[simp]
theorem fractionRing_equiv_pi_minimalPrimeLocalizations_apply_algebraMap
    (hzdiv :
      (⋃ p : minimalPrimes R, (p.1 : Set R)) =
        {x : R | x ∉ nonZeroDivisors R})
    (r : R) :
    fractionRing_equiv_pi_minimalPrimeLocalizations R hzdiv
        (algebraMap R (FractionRing R) r) =
      algebraMap R (∀ p : minimalPrimes R, Localization.AtPrime p.1) r := sorry

@[stacks 00E3 "spectrum of a localization"]
#check @PrimeSpectrum.localizationHomeomorph

#check @Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes

end
