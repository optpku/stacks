/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.IrreducibleComponents
import StacksCheckRecall

@[expose] public section

universe u

variable (A : Type u) [CommRing A]

/- Exercise 111.6.21: irreducible components of `PrimeSpectrum A` correspond to
minimal primes of `A`. -/
@[stacks 02DC]
#check (PrimeSpectrum.irreducibleComponentsEquivMinimalPrimes A :
  irreducibleComponents (PrimeSpectrum A) ≃ minimalPrimes A)

/- Companion: the image of `minimalPrimes` under `zeroLocus` is exactly
`irreducibleComponents (PrimeSpectrum A)`. -/
#check (PrimeSpectrum.zeroLocus_minimalPrimes A :
  (fun ideal : Ideal A ↦ PrimeSpectrum.zeroLocus (ideal : Set A)) '' minimalPrimes A =
    irreducibleComponents (PrimeSpectrum A))

/- Companion: the image of `irreducibleComponents` under `vanishingIdeal` is exactly
`minimalPrimes A`. -/
#check (PrimeSpectrum.vanishingIdeal_irreducibleComponents A :
  PrimeSpectrum.vanishingIdeal '' irreducibleComponents (PrimeSpectrum A) = minimalPrimes A)
