module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Irreducibility of Prime Spectra

This leaf records the ring-level form of the unique-minimal-prime criterion.  The
criterion is independent of a chosen presentation or a field, so it lives next
to the canonical `PrimeSpectrum` topology rather than in an algebraic-geometry
chapter.

@stack 00I7
@stack 04MG
-/

@[expose] public section

open PrimeSpectrum

universe u

namespace PrimeSpectrum

variable {R : Type u} [CommRing R]

/-- A unique minimal prime makes the prime spectrum irreducible. -/
@[stacks 00I7 "unique minimal-prime criterion, forward direction"]
theorem irreducible_of_unique_minimalPrime
    (h : ∃! p : Ideal R, p ∈ minimalPrimes R) :
    IrreducibleSpace (PrimeSpectrum R) := sorry

/-- An irreducible prime spectrum has a unique minimal prime. -/
@[stacks 00I7 "unique minimal-prime criterion, reverse direction"]
theorem unique_minimalPrime_of_irreducible
    (h : IrreducibleSpace (PrimeSpectrum R)) :
    ∃! p : Ideal R, p ∈ minimalPrimes R := sorry

/-- The prime spectrum is irreducible exactly when its ring has one minimal prime. -/
@[stacks 00I7]
theorem irreducible_iff_unique_minimalPrime :
    IrreducibleSpace (PrimeSpectrum R) ↔
      ∃! p : Ideal R, p ∈ minimalPrimes R := sorry

/-- A point is the generic point of its irreducible component exactly when it
corresponds to a minimal prime ideal. -/
@[stacks 04MG "minimal-prime generic-point bridge"]
theorem isGenericPoint_irreducibleComponent_iff_mem_minimalPrimes
    (p : PrimeSpectrum R) :
    IsGenericPoint p (irreducibleComponent p) ↔ p.asIdeal ∈ minimalPrimes R := sorry

/-- A closed subset of a prime spectrum is irreducible exactly when it is the
zero locus of a prime ideal. -/
@[stacks 02D5]
theorem isIrreducible_iff_exists_isPrime_zeroLocus {R : Type u} [CommSemiring R]
    {T : Set (PrimeSpectrum R)} (hT : IsClosed T) :
    IsIrreducible T ↔ ∃ p : Ideal R, p.IsPrime ∧ T = zeroLocus p := sorry

end PrimeSpectrum
