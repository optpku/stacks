/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.Unibranch
public import ReasLib.RingTheory.Spectrum.Prime.UniqueMinimalPrime
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Minimal primes of unibranch local rings

Unibranchness contains a canonical domain-reduction condition. This leaf exposes its immediate
minimal-prime consequences as reusable instance and theorem API.
@stack 0BPZ
-/

@[expose] public section

open Ideal

universe u

namespace IsUnibranch

variable {A : Type u} [CommRing A]

/-- The nilradical of a unibranch local ring is prime. -/
@[stacks 0BPZ "prime nilradical of a unibranch local ring"]
instance isPrime_nilradical [IsUnibranch A] : (nilradical A).IsPrime := sorry

/-- The nilradical is the only minimal prime of a unibranch local ring. -/
@[stacks 0BPZ "minimal primes of a unibranch local ring"]
theorem minimalPrimes_eq_singleton_nilradical [IsUnibranch A] :
    minimalPrimes A = {nilradical A} := sorry

/-- A unibranch local ring has a unique minimal prime. -/
@[stacks 0BPZ "unique minimal prime of a unibranch local ring"]
theorem uniqueMinimalPrime [IsUnibranch A] :
    ∃! p : Ideal A, p ∈ minimalPrimes A := sorry

end IsUnibranch
