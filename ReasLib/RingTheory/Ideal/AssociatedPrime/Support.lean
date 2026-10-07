module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Support
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module
import Mathlib.Tactic.CrossRefAttribute

/-!
# Minimal support points and associated primes

This leaf compares minimal points using one carrier, `PrimeSpectrum R`.  The associated-prime
sets consist of ideals, so their point views are formed by preimage along
`PrimeSpectrum.asIdeal`.  This avoids transporting `Minimal` between ideals and bundled prime
points in every downstream filtration or dimension argument.
-/

@[expose] public section

universe u v

namespace Module

/-- Stacks `05BV`: a minimal point of module support is an associated prime over a Noetherian
ring.  No finite-generation hypothesis on the module is needed. -/
@[stacks 05BV "minimal support points are associated"]
theorem minimal_support_mem_associatedPrimes
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (p : PrimeSpectrum R) (hp : Minimal (· ∈ support R M) p) :
    p.asIdeal ∈ associatedPrimes R M := sorry

end Module

namespace associatedPrimes

/-- Stacks `02CE`: the minimal associated-prime points are exactly the minimal points of module
support.  Both sides use `PrimeSpectrum R`, making this the canonical rewrite interface. -/
@[stacks 02CE "minimal associated-prime points and support"]
theorem minimal_point_iff_minimal_support
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (p : PrimeSpectrum R) :
    Minimal (· ∈ PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R M) p ↔
      Minimal (· ∈ Module.support R M) p := sorry

end associatedPrimes

namespace associatedPrimesOfModule

/-- Stacks `02CE`: over a Noetherian ring, the minimal exact-associated-prime points are exactly
the minimal points of module support. -/
@[stacks 02CE "minimal exact-associated-prime points and support"]
theorem minimal_point_iff_minimal_support
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (p : PrimeSpectrum R) :
    Minimal (· ∈ PrimeSpectrum.asIdeal ⁻¹' associatedPrimesOfModule R M) p ↔
      Minimal (· ∈ Module.support R M) p := sorry

end associatedPrimesOfModule

/-- Proposition 10.63.6 compatibility bridge: the textbook ideal-level formulation of minimal
associated primes.  New infrastructure should use `associatedPrimes.minimal_point_iff_minimal_support`
so both predicates live on `PrimeSpectrum R`. -/
@[stacks 02CE "minimal support and associated ideals"]
theorem minimal_support_iff_minimal_associatedPrimes
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : PrimeSpectrum R) :
    Minimal (· ∈ Module.support R M) p ↔
      Minimal (· ∈ associatedPrimes R M) p.asIdeal := sorry
