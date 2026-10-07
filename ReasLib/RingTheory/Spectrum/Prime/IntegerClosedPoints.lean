module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.JacobsonSpace

@[expose] public section

namespace PrimeSpectrum

/-- The set of closed points of `PrimeSpectrum ℤ` is irreducible. -/
theorem isIrreducible_closedPoints_int : IsIrreducible (closedPoints (PrimeSpectrum ℤ)) := sorry

/-- The closed points of `PrimeSpectrum ℤ` are not contained in the closure of any one of
their points. -/
theorem closedPoints_int_not_subset_closure_singleton {x : PrimeSpectrum ℤ}
    (hx : x ∈ closedPoints (PrimeSpectrum ℤ)) :
    ¬ closedPoints (PrimeSpectrum ℤ) ⊆ closure {x} := sorry

end PrimeSpectrum
