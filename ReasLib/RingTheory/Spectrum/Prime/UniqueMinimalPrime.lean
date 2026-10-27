/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.RingTheory.Spectrum.Prime.Irreducible
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Rings with a unique minimal prime

This file collects the canonical ring-theoretic forms of the condition that a prime spectrum has
one generic point. The quotient by the nilradical is used directly, so this API is independent of
any chapter-specific name for the reduction.
-/

@[expose] public section

universe u

namespace PrimeSpectrum.UniqueMinimalPrime

variable {R : Type u} [CommRing R]

/-- A commutative ring has a unique minimal prime exactly when its nilradical is prime. -/
theorem iff_isPrime_nilradical :
    (∃! p : Ideal R, p ∈ minimalPrimes R) ↔ (nilradical R).IsPrime := sorry

/-- A commutative ring has a unique minimal prime exactly when its reduction is a domain. -/
theorem iff_isDomain_quotient_nilradical :
    (∃! p : Ideal R, p ∈ minimalPrimes R) ↔
      IsDomain (R ⧸ nilradical R) := sorry

/-- A commutative ring has a unique minimal prime exactly when the nilradical is its only
minimal prime. -/
theorem iff_minimalPrimes_eq_singleton_nilradical :
    (∃! p : Ideal R, p ∈ minimalPrimes R) ↔
      minimalPrimes R = {nilradical R} := sorry

end PrimeSpectrum.UniqueMinimalPrime

namespace PrimeSpectrum.UniqueMinimalPrime

variable {R : Type u} [CommSemiring R]

/-- A prime nilradical is the only minimal prime of a commutative semiring. -/
theorem minimalPrimes_eq_singleton_nilradical_of_isPrime
    (h : (nilradical R).IsPrime) : minimalPrimes R = {nilradical R} := sorry

end PrimeSpectrum.UniqueMinimalPrime
