/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.Localization.BaseChange
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.BaseChange
public import ReasLib.RingTheory.Smooth.NeronBlowup.Core

/-!
# Localization of affine Neron blowups

This file records the localized factorization and the base-change comparison
away from the closed center.
-/

@[expose] public section

noncomputable section

open Ideal IsLocalRing
open scoped AffineBlowupChart TensorProduct

universe u v

namespace Algebra.DVR.Factorization

variable {R : Type u} {L : Type v}
variable [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [CommRing L] [IsDomain L] [IsDiscreteValuationRing L]
variable [Algebra R L]

/-- Away from the closed center, the factorization map sends every denominator to a unit. -/
@[stacks 0BJ3 "localization denominator unit"]
theorem localizationDenominator_isUnit
    (S : Algebra.DVR.Factorization R L) (a : S.mid) (ha : a ∉ S.closedIdeal)
    (y : Submonoid.powers a) :
    IsUnit ((Algebra.ofId S.mid L) y) := sorry

/-- The factorization map extends canonically across localization away from
an element outside the closed center. -/
@[stacks 0BJ3 "localized factorization map"]
noncomputable def localizationMap
    (S : Algebra.DVR.Factorization R L) (a : S.mid) (ha : a ∉ S.closedIdeal) :
    Localization.Away a →ₐ[S.mid] L :=
  IsLocalization.liftAlgHom (localizationDenominator_isUnit S a ha)

/-- The closed center of the localized factorization. -/
@[stacks 0BJ3 "localized closed center"]
def localizationCenter
    (S : Algebra.DVR.Factorization R L) (a : S.mid) (ha : a ∉ S.closedIdeal) :
    Ideal (Localization.Away a) :=
  Ideal.comap (S.localizationMap a ha).toRingHom (maximalIdeal L)

/-- The localized closed center is the extension of the original closed center. -/
theorem localizationCenter_eq_map
    (S : Algebra.DVR.Factorization R L) (a : S.mid) (ha : a ∉ S.closedIdeal) :
    S.localizationCenter a ha =
      Ideal.map (algebraMap S.mid (Localization.Away a)) S.closedIdeal := sorry

/-- The localized image of a uniformizer belongs to the localized closed center. -/
theorem localizationParameter_mem
    [IsExtensionOfDiscreteValuationRings R L]
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π)
    (a : S.mid) (ha : a ∉ S.closedIdeal) :
    algebraMap R (Localization.Away a) π ∈ S.localizationCenter a ha := sorry

/-- The image of a uniformizer in the localized closed center. -/
@[stacks 0BJ3 "localized uniformizer"]
def localizationParameter
    [IsExtensionOfDiscreteValuationRings R L]
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π)
    (a : S.mid) (ha : a ∉ S.closedIdeal) : S.localizationCenter a ha :=
  ⟨algebraMap R (Localization.Away a) π, S.localizationParameter_mem π hπ a ha⟩

/-- Lemma 16.4.2 (1) (tag 0BJ3): the canonical base-change comparison for an affine Neron
blowup is bijective after localizing away from an element outside the closed center. -/
@[stacks 0BJ3]
theorem localizationComparison_bijective
    [IsExtensionOfDiscreteValuationRings R L]
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π)
    (a : S.mid) (ha : a ∉ S.closedIdeal) :
    Function.Bijective
      (AffineBlowupChart.BaseChange.tensorMap (Localization.Away a) S.closedIdeal
        (S.neronBlowupParameter π hπ)) := sorry

end Algebra.DVR.Factorization
