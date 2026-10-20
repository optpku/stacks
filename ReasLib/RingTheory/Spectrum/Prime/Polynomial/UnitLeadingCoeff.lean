/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Polynomial
import Mathlib.Tactic.CrossRefAttribute

/-!
# Polynomial Spectrum Images with Unit Leading Coefficient

The monic polynomial image theorems extend to polynomials whose leading coefficient is a unit by
normalizing the polynomial with that unit.

@stack 00FD
-/

@[expose] public section

open Polynomial PrimeSpectrum
open scoped Pointwise

universe u

namespace Polynomial

variable {R : Type u} [CommRing R]

namespace UnitLeadingCoeff

/-- Scaling by the inverse of a unit leading coefficient does not change the zero locus. -/
@[simp, stacks 00FD "zero locus after unit-leading-coefficient normalization"]
theorem zeroLocus_inv_smul
    (g : R[X]) (hg : IsUnit g.leadingCoeff) :
    (zeroLocus ({hg.unit⁻¹ • g} : Set R[X]) : Set (PrimeSpectrum R[X])) =
      zeroLocus ({g} : Set R[X]) := by
  rw [show hg.unit⁻¹ • g = C (↑(hg.unit⁻¹) : R) * g by
    ext i
    simp [coeff_C_mul, Units.smul_def]]
  simpa [smul_eq_mul] using
    (PrimeSpectrum.zeroLocus_smul_of_isUnit
      (R := R[X]) (isUnit_C.mpr (Units.isUnit _)) ({g} : Set R[X]))

end UnitLeadingCoeff

/-- The image theorem for a monic polynomial extends to a polynomial with unit leading
coefficient. -/
@[stacks 00FD "polynomial spectrum image with unit leading coefficient"]
theorem exists_image_comap_of_isUnit_leadingCoeff
    (f g : R[X]) (hg : IsUnit g.leadingCoeff) :
    ∃ t : Finset R,
      comap C '' (zeroLocus ({g} : Set R[X]) \ zeroLocus ({f} : Set R[X])) =
        (zeroLocus t : Set (PrimeSpectrum R))ᶜ := by
  have hmonic : (hg.unit⁻¹ • g).Monic :=
    monic_of_isUnit_leadingCoeff_inv_smul hg
  simpa only [UnitLeadingCoeff.zeroLocus_inv_smul g hg] using
    exists_image_comap_of_monic f (hg.unit⁻¹ • g) hmonic

/-- The corresponding image in the base spectrum is compact. -/
@[stacks 00FD "compact polynomial spectrum image with unit leading coefficient"]
theorem isCompact_image_comap_of_isUnit_leadingCoeff
    (f g : R[X]) (hg : IsUnit g.leadingCoeff) :
    IsCompact (comap C ''
      (zeroLocus ({g} : Set R[X]) \ zeroLocus ({f} : Set R[X]))) := by
  obtain ⟨t, ht⟩ := exists_image_comap_of_isUnit_leadingCoeff f g hg
  rw [ht, ← (t : Set R).iUnion_of_singleton_coe, zeroLocus_iUnion, Set.compl_iInter]
  apply isCompact_iUnion
  exact fun _ ↦ by simpa using isCompact_basicOpen _

/-- The corresponding image in the base spectrum is open. -/
@[stacks 00FD "open polynomial spectrum image with unit leading coefficient"]
theorem isOpen_image_comap_of_isUnit_leadingCoeff
    (f g : R[X]) (hg : IsUnit g.leadingCoeff) :
    IsOpen (comap C ''
      (zeroLocus ({g} : Set R[X]) \ zeroLocus ({f} : Set R[X]))) := by
  obtain ⟨t, ht⟩ := exists_image_comap_of_isUnit_leadingCoeff f g hg
  rw [ht]
  exact (isClosed_zeroLocus (R := R) t).isOpen_compl

namespace UnitLeadingCoeff

/-- The image is a finite union of basic opens in the base spectrum. -/
@[stacks 00FD "finite basic-open cover of the polynomial spectrum image"]
theorem exists_iUnion_basicOpen
    (f g : R[X]) (hg : IsUnit g.leadingCoeff) :
    ∃ t : Finset R,
      comap C '' ((basicOpen f : Set (PrimeSpectrum R[X])) ∩ zeroLocus ({g} : Set R[X])) =
        ⋃ r ∈ t, (basicOpen r : Set (PrimeSpectrum R)) := by
  obtain ⟨t, ht⟩ := Polynomial.exists_image_comap_of_isUnit_leadingCoeff f g hg
  refine ⟨t, ?_⟩
  rw [show
    (basicOpen f : Set (PrimeSpectrum R[X])) ∩ zeroLocus ({g} : Set R[X]) =
      zeroLocus ({g} : Set R[X]) \ zeroLocus ({f} : Set R[X]) by
    ext x
    simp [basicOpen_eq_zeroLocus_compl, and_comm]]
  rw [ht]
  ext p
  simp [basicOpen_eq_zeroLocus_compl, Set.not_subset]

end UnitLeadingCoeff

end Polynomial
