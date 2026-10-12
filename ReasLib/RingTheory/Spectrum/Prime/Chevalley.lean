/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Chevalley

@[expose] public section

universe u v

namespace PrimeSpectrum

/-- A finite-presentation ring homomorphism sends constructible subsets of the
target spectrum to constructible subsets of the source spectrum. -/
theorem isConstructible_comap_image_of_finitePresentation
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : f.FinitePresentation) {s : Set (PrimeSpectrum S)}
    (hs : Topology.IsConstructible s) :
    Topology.IsConstructible (PrimeSpectrum.comap f '' s) := sorry

end PrimeSpectrum
