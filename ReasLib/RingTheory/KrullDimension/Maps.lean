/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.KrullDimension.Maps

@[expose] public section

/-!
# Krull dimension under maps of spectra

This leaf transports the topological dimension comparison for a surjective
spectral map that lifts specializations or generalizations to the associated
ring-theoretic Krull dimensions.

@stack 00OH
-/

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring map whose map on prime spectra is surjective and lifts one
direction of specialization does not decrease Krull dimension. -/
@[stacks 00OH "Krull dimension under a surjective spectral map"]
theorem ringKrullDim_le_of_comap_surjective_of_specializing_or_generalizing
    (f : R →+* S) (h_surjective : Function.Surjective (PrimeSpectrum.comap f))
    (h_lift : SpecializingMap (PrimeSpectrum.comap f) ∨
      GeneralizingMap (PrimeSpectrum.comap f)) :
    ringKrullDim R ≤ ringKrullDim S := sorry

/-- The going-up case of the ring-theoretic Krull-dimension comparison. -/
@[stacks 00OH "going-up case"]
theorem ringKrullDim_le_of_comap_surjective_of_specializing
    (f : R →+* S) (h_surjective : Function.Surjective (PrimeSpectrum.comap f))
    (h_specializing : SpecializingMap (PrimeSpectrum.comap f)) :
    ringKrullDim R ≤ ringKrullDim S := sorry

/-- The going-down case of the ring-theoretic Krull-dimension comparison. -/
@[stacks 00OH "going-down case"]
theorem ringKrullDim_le_of_comap_surjective_of_generalizing
    (f : R →+* S) (h_surjective : Function.Surjective (PrimeSpectrum.comap f))
    (h_generalizing : GeneralizingMap (PrimeSpectrum.comap f)) :
    ringKrullDim R ≤ ringKrullDim S := sorry

end RingHom
