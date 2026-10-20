module

public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.Topology.Artinian

@[expose] public section

universe u

namespace PrimeSpectrum

/-- The prime spectrum of an Artinian commutative semiring is an Artinian topological space. -/
instance instArtinianSpace {R : Type u} [CommSemiring R] [IsArtinianRing R] :
    TopologicalSpace.ArtinianSpace (PrimeSpectrum R) := sorry

end PrimeSpectrum
