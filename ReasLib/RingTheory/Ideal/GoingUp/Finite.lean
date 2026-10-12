/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

@[expose] public section

universe u v

namespace Ideal

/-- For a finite algebra, a prime whose contraction is contained in a base
prime is contained in a prime contracting to that base prime. -/
theorem exists_prime_over_of_finite
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] (basePrime : Ideal R) [basePrime.IsPrime]
    (prime : Ideal S) [prime.IsPrime]
    (h_contraction : prime.comap (algebraMap R S) ≤ basePrime) :
    ∃ overPrime ≥ prime, overPrime.IsPrime ∧
      overPrime.comap (algebraMap R S) = basePrime := sorry

end Ideal
