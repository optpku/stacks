/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Closed-point criteria for faithfully flat ring maps

@stack 00HQ

This leaf turns the topological closed-point criterion for a generalizing map
into a ring-hom criterion for flat and faithfully flat maps.
-/

universe u v

section

open PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- For a flat ring map, the induced map
of prime spectra is surjective exactly when its image contains every closed
point of the source spectrum. -/
@[stacks 00HQ]
theorem specComap_surjective_iff_closedPoints_subset_range (f : R →+* S) (hf : f.Flat) :
    Function.Surjective (comap f) ↔
      closedPoints (PrimeSpectrum R) ⊆ Set.range (comap f) := sorry

/-- A flat ring map is faithfully flat exactly when the image
of its prime spectrum map contains every closed point of the source spectrum. -/
@[stacks 00HQ]
theorem faithfullyFlat_iff_closedPoints_subset_range (f : R →+* S) (hf : f.Flat) :
    f.FaithfullyFlat ↔ closedPoints (PrimeSpectrum R) ⊆ Set.range (comap f) := sorry

end
