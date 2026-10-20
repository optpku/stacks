/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Restriction
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived-complete restriction equivalences

Restriction of scalars carries objects complete for `I.map σ` to objects complete for `I`.
This leaf owns the resulting functor between the derived-complete full subcategories and the flat
quotient criterion which makes it an equivalence.

@stack 0925
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace DerivedCategory.DerivedComplete.Restriction

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Restriction of scalars along `σ` on the full subcategories of derived-complete objects. -/
@[stacks 0925 "restriction on derived-complete full subcategories"]
abbrev functor (σ : A →+* B) (I : Ideal A) :
    (derivedCompleteObjectProperty (I.map σ)).FullSubcategory ⥤
      (derivedCompleteObjectProperty I).FullSubcategory :=
  ObjectProperty.FullSubcategory.restrict
    (ModuleCat.restrictScalars σ).mapDerivedCategory
    (fun L hL ↦
      (isDerivedCompleteWithRespectTo_iff_restrictScalars σ L I).2 hL)

/-- Lemma 15.92.25 (Stacks `0925`): if `σ : A →+* B` is flat and induces a bijection
`A ⧸ I → B ⧸ I.map σ`, then restriction of scalars is an equivalence between the corresponding
derived-complete full subcategories. -/
@[stacks 0925 "flat quotient comparison gives a derived-complete equivalence"]
theorem isEquivalence_of_flat_of_quotientMap_bijective
    (σ : A →+* B) (I : Ideal A) (hσ : σ.Flat) (hI : I.FG)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map σ) σ Ideal.le_comap_map)) :
    (functor σ I).IsEquivalence := sorry

end DerivedCategory.DerivedComplete.Restriction
