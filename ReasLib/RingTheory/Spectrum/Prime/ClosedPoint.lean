module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.JacobsonSpace

@[expose] public section

universe u

namespace PrimeSpectrum

/-- A point of the prime spectrum of a commutative semiring is closed if and only if its
underlying ideal is maximal. -/
theorem mem_closedPoints_iff_isMaximal {R : Type u} [CommSemiring R] (x : PrimeSpectrum R) :
    x ∈ closedPoints (PrimeSpectrum R) ↔ x.asIdeal.IsMaximal := sorry

end PrimeSpectrum
