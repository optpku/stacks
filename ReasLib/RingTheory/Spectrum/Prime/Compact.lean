module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.Topology.Compactness.Basic

@[expose] public section

universe u

namespace PrimeSpectrum

/-- The prime spectrum of a commutative semiring is quasi-compact in the Zariski topology. -/
theorem isQuasiCompact (R : Type u) [CommSemiring R] :
    TopologicalSpace.IsQuasiCompact (PrimeSpectrum R) := by
  exact isCompact_univ

end PrimeSpectrum
