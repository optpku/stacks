/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.JacobsonSpace

@[expose] public section

universe u

namespace PrimeSpectrum

/-- A point of the prime spectrum of a commutative ring is closed if and only if its
underlying ideal is maximal. -/
theorem mem_closedPoints_iff_isMaximal {R : Type u} [CommRing R] (x : PrimeSpectrum R) :
    x ∈ closedPoints (PrimeSpectrum R) ↔ x.asIdeal.IsMaximal := sorry

end PrimeSpectrum
