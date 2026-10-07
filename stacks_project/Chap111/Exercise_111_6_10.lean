module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.6.10 (1): `Spec(A)` is irreducible if and only if `Nil(A)` is a prime
ideal. Mathlib owns this as `PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`. -/
@[stacks 02D4]
#check @PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical

/-- Exercise 111.6.10 (2): if `nilradical R` is prime, then it is the unique
minimal prime of `R`. -/
@[stacks 02D4]
theorem minimalPrimes_eq_singleton_nilradical_of_isPrime {R : Type u} [CommSemiring R]
    (h : (nilradical R).IsPrime) : minimalPrimes R = {nilradical R} := sorry

