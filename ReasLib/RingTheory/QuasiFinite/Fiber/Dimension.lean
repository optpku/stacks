module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.KrullDimension.Fiber.MinimalPrime

@[expose] public section

/-!
# Quasi-finiteness and fiber dimension

@stack 04GG

This leaf relates quasi-finiteness at points over an arbitrary base prime to
the dimensions of the irreducible components of the corresponding
residue-field fiber.  The statements do not require the base ring to be
local, so closed-fiber specializations belong in downstream applications.
-/

universe u v

namespace Algebra.QuasiFiniteAt

/-- For a finite-type algebra over a field, quasi-finiteness at `q` is
equivalent to `q` being a minimal prime with zero-dimensional quotient. -/
@[stacks 04GG "quasi-finite point of a field-valued fiber"]
theorem iff_minimalPrime_and_ringKrullDim_eq_zero
    {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] (q : PrimeSpectrum A) :
    Algebra.QuasiFiniteAt K q.asIdeal ↔
      q.asIdeal ∈ minimalPrimes A ∧
        ringKrullDim (A ⧸ q.asIdeal) = 0 := sorry

/-- For a finite-type algebra, no prime over `p` is quasi-finite exactly when every
minimal prime of the residue-field fiber over `p` has positive-dimensional
quotient. -/
@[stacks 04GG "non-quasi-finite fiber criterion"]
theorem not_at_primesOver_iff_minimalPrimes_positiveDimensional
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (p : PrimeSpectrum R) :
    (∀ q : PrimeSpectrum S,
        p.asIdeal = Ideal.comap (algebraMap R S) q.asIdeal →
          ¬ Algebra.QuasiFiniteAt R q.asIdeal) ↔
      Algebra.Fiber.minimalPrimesPositiveDimensional (S := S) p := sorry

end Algebra.QuasiFiniteAt
