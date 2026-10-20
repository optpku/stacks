module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs

@[expose] public section

universe u

namespace IsLocalRing

/-- A quotient of a commutative local ring has a singleton prime spectrum
exactly when the radical of the quotient ideal is the maximal ideal. -/
theorem unique_primeSpectrum_quotient_iff {R : Type u} [CommRing R] [IsLocalRing R]
    (J : Ideal R) :
    Nonempty (Unique (PrimeSpectrum (R ⧸ J))) ↔ J.radical = maximalIdeal R :=
  sorry

end IsLocalRing
