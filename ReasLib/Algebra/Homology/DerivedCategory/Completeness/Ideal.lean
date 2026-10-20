/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.LocalizationAway
import Mathlib.Tactic.CrossRefAttribute

/-!
# The localization-away vanishing ideal

The elements which kill the localization-away derived-Hom condition form a radical ideal.  The
carrier is kept explicit, while closure and radicality are exposed as separate proposition-valued
APIs.  This lets derived-completeness and restriction-of-scalars owners reuse the ideal without
importing a chapter proof route.

@stack 091Q
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace DerivedCategory

variable {A : Type u} [CommRing A]

/-- Lemma 15.92.2 (Stacks `091Q`): the localization-away condition holds at zero. -/
@[stacks 091Q "zero belongs to the localization-away vanishing locus"]
theorem localizationAwayDerivedHomVanishingCondition_zero
    (K : DerivedCategory (ModuleCat A)) :
    localizationAwayDerivedHomVanishingCondition 0 K := sorry

/-- The localization-away vanishing condition is stable under addition. -/
@[stacks 091Q "addition in the localization-away vanishing locus"]
theorem localizationAwayDerivedHomVanishingCondition_add
    {f g : A} {K : DerivedCategory (ModuleCat A)}
    (hf : localizationAwayDerivedHomVanishingCondition f K)
    (hg : localizationAwayDerivedHomVanishingCondition g K) :
    localizationAwayDerivedHomVanishingCondition (f + g) K := sorry

/-- The localization-away vanishing condition is stable under multiplication by a scalar. -/
@[stacks 091Q "scalar multiplication in the localization-away vanishing locus"]
theorem localizationAwayDerivedHomVanishingCondition_smul
    (r : A) {f : A} {K : DerivedCategory (ModuleCat A)}
    (hf : localizationAwayDerivedHomVanishingCondition f K) :
    localizationAwayDerivedHomVanishingCondition (r • f) K := sorry

/-- A positive power in the localization-away vanishing locus implies its base is in the locus. -/
@[stacks 091Q "power stability of the localization-away vanishing locus"]
theorem localizationAwayDerivedHomVanishingCondition_of_pow
    {f : A} {n : ℕ} {K : DerivedCategory (ModuleCat A)}
    (hnpos : 0 < n)
    (hf : localizationAwayDerivedHomVanishingCondition (f ^ n) K) :
    localizationAwayDerivedHomVanishingCondition f K := sorry

/-- Lemma 15.92.2 (Stacks `091Q`): the localization-away vanishing ideal has the displayed
condition as its explicit carrier. -/
@[stacks 091Q "localization-away vanishing ideal"]
def localizationAwayDerivedHomVanishingIdeal
    (K : DerivedCategory (ModuleCat A)) : Ideal A where
  carrier := {f : A | localizationAwayDerivedHomVanishingCondition f K}
  zero_mem' := localizationAwayDerivedHomVanishingCondition_zero K
  add_mem' := fun hf hg ↦ localizationAwayDerivedHomVanishingCondition_add hf hg
  smul_mem' := fun r _ hf ↦ localizationAwayDerivedHomVanishingCondition_smul r hf

/-- Membership in the localization-away vanishing ideal is exactly the defining vanishing
condition. -/
@[stacks 091Q "membership in the localization-away vanishing ideal"]
theorem mem_localizationAwayDerivedHomVanishingIdeal_iff
    (K : DerivedCategory (ModuleCat A)) (f : A) :
    f ∈ K.localizationAwayDerivedHomVanishingIdeal ↔
      localizationAwayDerivedHomVanishingCondition f K := sorry

/-- Lemma 15.92.2 (Stacks `091Q`): the localization-away vanishing ideal is radical. -/
@[stacks 091Q "radicality of the localization-away vanishing ideal"]
theorem localizationAwayDerivedHomVanishingIdeal_isRadical
    (K : DerivedCategory (ModuleCat A)) :
    K.localizationAwayDerivedHomVanishingIdeal.IsRadical := sorry

end DerivedCategory
