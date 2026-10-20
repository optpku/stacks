/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.CompositionSeries.Localization
public import ReasLib.Algebra.Module.CompositionSeries.ResidueField
public import ReasLib.Algebra.Module.CompositionSeries.RestrictScalars

/-!
# Length under a local base ring

This file owns the residue-degree formula for restricting a finite-length module
along an algebra over a local ring. The primary statement uses `finsum`, so its
interface does not depend on an arbitrary enumeration of maximal ideals.

@stack 02M0
-/

@[expose] public section

open scoped BigOperators
open IsLocalRing

universe u v w

namespace Module

variable {A : Type u} {B : Type v} {M : Type w}
variable [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B]
variable [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

/-- The length over a local base is the finitely supported sum of the local lengths over the
algebra, weighted by the inertia degrees of the corresponding residue fields. No enumeration of
the maximal spectrum is part of this canonical statement. -/
@[stacks 02M0 "enumeration-free residue-degree length formula"]
theorem length_eq_finsum_inertiaDeg_mul_localized
    (hclosed : ∀ m : MaximalSpectrum B, m.asIdeal.under A = maximalIdeal A)
    (hfinite : ∀ m : MaximalSpectrum B,
      (Ideal.ResidueField.mapUnder A m.asIdeal).Finite)
    (hM : IsFiniteLength B M) :
    Module.length A M =
      ∑ᶠ m : MaximalSpectrum B,
        (m.asIdeal.inertiaDeg A : ℕ∞) *
          Module.length (Localization.AtPrime m.asIdeal)
            (LocalizedModule.AtPrime m.asIdeal M) := sorry

/-- Finite maximal-spectrum specialization of
`Module.length_eq_finsum_inertiaDeg_mul_localized`. -/
@[stacks 02M0 "finite maximal-spectrum residue-degree length formula"]
theorem length_eq_sum_inertiaDeg_mul_localized
    [Fintype (MaximalSpectrum B)]
    (hclosed : ∀ m : MaximalSpectrum B, m.asIdeal.under A = maximalIdeal A)
    (hfinite : ∀ m : MaximalSpectrum B,
      (Ideal.ResidueField.mapUnder A m.asIdeal).Finite)
    (hM : IsFiniteLength B M) :
    Module.length A M =
      ∑ m : MaximalSpectrum B,
        (m.asIdeal.inertiaDeg A : ℕ∞) *
          Module.length (Localization.AtPrime m.asIdeal)
            (LocalizedModule.AtPrime m.asIdeal M) := sorry

/-- Finite length descends to the local base when every occurring residue-field map is finite.
The statement does not require the whole maximal spectrum to be finite. -/
@[stacks 02M0 "finite length after restriction to a local base"]
theorem isFiniteLength_restrictScalars_of_residueFinite
    (hclosed : ∀ m : MaximalSpectrum B, m.asIdeal.under A = maximalIdeal A)
    (hfinite : ∀ m : MaximalSpectrum B,
      (Ideal.ResidueField.mapUnder A m.asIdeal).Finite)
    (hM : IsFiniteLength B M) :
    IsFiniteLength A M := sorry

end Module
