/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import ReasLib.RingTheory.Spectrum.Prime.Constructible.FiniteType
public import ReasLib.RingTheory.Spectrum.Prime.Jacobson.FiniteType

/-!
# Closed points in constructible spectrum images

For a finite-type map out of a Jacobson ring, this leaf compares the closed points of a
constructible image with the image of the closed-point trace.  The target is automatically
Jacobson, so that consequence is not exposed as a redundant typeclass parameter.  The leaf also
records the corresponding density test for membership in the image.

@stack 00GD
-/

@[expose] public section

universe u v

open Set Topology

namespace PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [IsJacobsonRing R]

/-- Lemma 10.35.21 (1): the closed points of the image of a constructible subset are precisely
the ambient images of its closed points. -/
@[stacks 00GD "(1), closed points of a constructible image"]
theorem closedPoints_comap_image
    (f : R →+* S) (hf : f.FiniteType) {E : Set (PrimeSpectrum S)}
    (hE : IsConstructible E) :
    Subtype.val '' closedPoints (comap f '' E) =
      (Subtype.val : closedPoints (PrimeSpectrum R) → PrimeSpectrum R) ''
        (comapClosedPoints f hf ''
          ((Subtype.val : closedPoints (PrimeSpectrum S) → PrimeSpectrum S) ⁻¹' E)) := sorry

/-- Tracing a constructible spectrum image to the closed-point subtype commutes with applying the
restricted spectrum map. -/
@[stacks 00GD "closed-point trace of a constructible image"]
theorem closedPointsTrace_comap_image
    (f : R →+* S) (hf : f.FiniteType) {E : Set (PrimeSpectrum S)}
    (hE : IsConstructible E) :
    (Subtype.val : closedPoints (PrimeSpectrum R) → PrimeSpectrum R) ⁻¹' (comap f '' E) =
      comapClosedPoints f hf ''
        ((Subtype.val : closedPoints (PrimeSpectrum S) → PrimeSpectrum S) ⁻¹' E) := sorry

/-- Lemma 10.35.21 (2): membership in the image of a constructible subset is detected by density
of the corresponding closed-point image in the closure of the point. -/
@[stacks 00GD "(2), dense closed-point trace"]
theorem mem_comap_image_iff_dense_closedPoints
    (f : R →+* S) (hf : f.FiniteType) {E : Set (PrimeSpectrum S)}
    {x : PrimeSpectrum R} (hE : IsConstructible E) :
    x ∈ comap f '' E ↔
      Dense
        ((Subtype.val : closure ({x} : Set (PrimeSpectrum R)) → PrimeSpectrum R) ⁻¹'
          ((Subtype.val : closedPoints (PrimeSpectrum R) → PrimeSpectrum R) ''
            (comapClosedPoints f hf ''
              ((Subtype.val : closedPoints (PrimeSpectrum S) → PrimeSpectrum S) ⁻¹' E)))) := sorry

end PrimeSpectrum
