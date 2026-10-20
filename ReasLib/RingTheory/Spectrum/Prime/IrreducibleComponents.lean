module

public import Mathlib.RingTheory.Spectrum.Prime.Topology

@[expose] public section

universe u

namespace PrimeSpectrum

/-- Irreducible components of the prime spectrum correspond to minimal prime ideals
via vanishing ideals, with inverse given by zero loci. -/
noncomputable def irreducibleComponentsEquivMinimalPrimes (R : Type u) [CommSemiring R] :
    irreducibleComponents (PrimeSpectrum R) ≃ minimalPrimes R :=
  (minimalPrimes.equivIrreducibleComponents R).toEquiv.symm

end PrimeSpectrum
