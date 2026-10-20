module

public import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.ConstructibleTopology.Maps

/-!
# Finite-Generator Forms of Constructible Prime-Spectrum Subsets

Mathlib's `PrimeSpectrum.ConstructibleSetData` is the canonical finite-data
presentation of a constructible subset.  This leaf exposes the equivalent
finite-generator form used naturally by commutative-algebra applications.

@stack 0G1P
@stack 00F7
@stack 00F8
-/

@[expose] public section

open Topology

universe u

namespace PrimeSpectrum.Constructible

variable {R : Type u} [CommSemiring R]

/-- Lemma 10.29.3 (Tag 0G1P): a subset of `PrimeSpectrum R` is constructible
exactly when it is a finite union of sets
`PrimeSpectrum.basicOpen f ∩ PrimeSpectrum.zeroLocus (G : Set R)`, with
`G : Finset R`.

This is the finite-generator companion to the canonical
`PrimeSpectrum.exists_constructibleSetData_iff`. -/
@[stacks 0G1P]
theorem iff_finset_union {T : Set (PrimeSpectrum R)} :
    IsConstructible T ↔
      ∃ s : Finset (R × Finset R),
        T = ⋃ a ∈ s,
          ((basicOpen a.1 : Set (PrimeSpectrum R)) ∩ zeroLocus (a.2 : Set R)) := sorry

end PrimeSpectrum.Constructible

namespace PrimeSpectrum

universe v

/-- Lemma 10.29.2 (1): the map on prime spectra induced by a ring homomorphism is spectral. -/
@[stacks 00F7 "(1), spectral map"]
theorem isSpectralMap_comap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    IsSpectralMap (comap f) := sorry

/-- Lemma 10.29.2 (2): inverse images under a map of prime spectra preserve constructible
subsets. -/
@[stacks 00F7 "(2), constructible preimage"]
theorem isConstructible_preimage_comap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) {E : Set (PrimeSpectrum R)} (hE : IsConstructible E) :
    IsConstructible (comap f ⁻¹' E) := sorry

/-- Lemma 10.29.4: every constructible subset of a prime spectrum is the image of the prime
spectrum of a finitely presented algebra. -/
@[stacks 00F8]
theorem exists_finitePresentation_range_eq_of_isConstructible
    {R : Type u} [CommRing R] {T : Set (PrimeSpectrum R)} (hT : IsConstructible T) :
    ∃ (S : Type u) (_ : CommRing S) (f : R →+* S),
      f.FinitePresentation ∧ Set.range (comap f) = T := sorry

end PrimeSpectrum
