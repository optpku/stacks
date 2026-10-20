module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Ideal
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Homology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived completeness and restriction of scalars

This leaf owns the generic restriction-of-scalars bridges for localization-away vanishing and
derived completeness.  The ring map is explicit, so the statements apply beyond a chosen bundled
`Algebra` instance; chapter files can specialize it to `algebraMap A B`.

@stack 0924
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace DerivedCategory

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Restriction of scalars along a ring map preserves and reflects zero derived objects. -/
@[stacks 0924 "restriction of scalars reflects zero derived objects"]
theorem isZero_restrictScalars_iff
    (σ : A →+* B) (K : DerivedCategory (ModuleCat B)) :
    IsZero (((ModuleCat.restrictScalars σ).mapDerivedCategory).obj K) ↔ IsZero K := sorry

/-- Restriction of scalars rewrites the localization-away vanishing condition by applying the ring
map to the element being inverted. -/
@[stacks 0924 "restriction of scalars and localization-away vanishing"]
theorem localizationAwayDerivedHomVanishingCondition_restrictScalars_iff
    (σ : A →+* B) (L : DerivedCategory (ModuleCat B)) (f : A) :
    localizationAwayDerivedHomVanishingCondition f
        (((ModuleCat.restrictScalars σ).mapDerivedCategory).obj L) ↔
      localizationAwayDerivedHomVanishingCondition (σ f) L := sorry

/-- The localization-away vanishing ideal after restriction is the comap of the vanishing ideal
over the target ring. -/
@[stacks 0924 "restriction of scalars and vanishing ideals"]
theorem localizationAwayDerivedHomVanishingIdeal_restrictScalars
    (σ : A →+* B) (L : DerivedCategory (ModuleCat B)) :
    (((ModuleCat.restrictScalars σ).mapDerivedCategory).obj L).localizationAwayDerivedHomVanishingIdeal =
      Ideal.comap σ L.localizationAwayDerivedHomVanishingIdeal := sorry

/-- Lemma 15.92.24 (Stacks `0924`): derived completeness pulls back along restriction of scalars
exactly as extension of the ideal. -/
@[stacks 0924 "derived completeness under restriction of scalars"]
theorem isDerivedCompleteWithRespectTo_iff_restrictScalars
    (σ : A →+* B) (L : DerivedCategory (ModuleCat B)) (I : Ideal A) :
    (((ModuleCat.restrictScalars σ).mapDerivedCategory).obj L).IsDerivedCompleteWithRespectTo I ↔
      L.IsDerivedCompleteWithRespectTo (I.map σ) := sorry

end DerivedCategory
