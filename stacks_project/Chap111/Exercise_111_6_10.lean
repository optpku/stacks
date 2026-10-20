/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.UniqueMinimalPrime
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.6.10 (1): `Spec(A)` is irreducible if and only if `Nil(A)` is a prime
ideal. -/
@[stacks 02D4] #check (PrimeSpectrum.UniqueMinimalPrime.irreducibleSpace_iff_isPrime_nilradical :
  ∀ {R : Type u} [CommSemiring R],
    IrreducibleSpace (PrimeSpectrum R) ↔ (nilradical R).IsPrime)

/- Exercise 111.6.10 (2): if `nilradical R` is prime, then it is the unique
minimal prime of `R`. -/
@[stacks 02D4] #check (PrimeSpectrum.UniqueMinimalPrime.minimalPrimes_eq_singleton_nilradical_of_isPrime :
  ∀ {R : Type u} [CommSemiring R],
    (nilradical R).IsPrime → minimalPrimes R = {nilradical R})
