/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Localization.Resolution
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.MorphismProperty.SaturatedMultiplicativeSystem
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Calculus

@[expose] public section

/-!
# Denominator Covers of Full Subcategories

This file expresses the two denominator-cover conditions for a full subcategory using mathlib's
`LocalizerMorphism.HasLeftResolutions` and `LocalizerMorphism.HasRightResolutions` interfaces.
Under saturation, either variance makes the induced localization functor an equivalence.  The
`_iff` bridges relate the standard resolution API to elementary full-subcategory formulations.
-/

universe v u

namespace CategoryTheory

open Localization MorphismProperty ObjectProperty

variable {D : Type u} [Category.{v} D]
  (P : ObjectProperty D) (S : MorphismProperty D)

namespace fullSubcategoryLocalizerMorphism

/-- Stacks 0GSL: left resolutions for the inclusion localizer are exactly denominator covers
of the ambient objects by `P.FullSubcategory`. -/
@[stacks 0GSL]
theorem hasLeftResolutions_iff :
    (fullSubcategoryLocalizerMorphism P S).HasLeftResolutions ↔
      ∀ X : D, ∃ (X' : P.FullSubcategory) (s : P.ι.obj X' ⟶ X), S s := sorry

/-- Stacks 0GSL: right resolutions for the inclusion localizer are exactly denominator
coreplacements of ambient objects by `P.FullSubcategory`. -/
@[stacks 0GSL "right resolutions for a full-subcategory inclusion"]
theorem hasRightResolutions_iff :
    (fullSubcategoryLocalizerMorphism P S).HasRightResolutions ↔
      ∀ X : D, ∃ (X' : P.FullSubcategory) (s : X ⟶ P.ι.obj X'), S s := sorry

end fullSubcategoryLocalizerMorphism

namespace fullSubcategoryLocalizationSystem.cover

/-- Stacks 0GSL: a saturated system restricted to a right-denominator-covering full
subcategory admits right fractions. -/
@[stacks 0GSL]
instance hasRightCalculusOfFractions [IsSaturatedMultiplicativeSystem S]
    [(fullSubcategoryLocalizerMorphism P S).HasLeftResolutions] :
    HasRightCalculusOfFractions (fullSubcategoryLocalizationSystem P S) := sorry

/-- Stacks 0GSL: a saturated system restricted to a left-denominator-covering full
subcategory admits left fractions. -/
@[stacks 0GSL "left fractions from right resolutions"]
instance hasLeftCalculusOfFractions [IsSaturatedMultiplicativeSystem S]
    [(fullSubcategoryLocalizerMorphism P S).HasRightResolutions] :
    HasLeftCalculusOfFractions (fullSubcategoryLocalizationSystem P S) := sorry

end fullSubcategoryLocalizationSystem.cover

namespace fullSubcategoryLocalizationFunctor.cover

/-- Stacks 0GSL: a right denominator cover makes the localized inclusion essentially
surjective. -/
@[stacks 0GSL]
theorem essSurj [(fullSubcategoryLocalizerMorphism P S).HasLeftResolutions] :
    (fullSubcategoryLocalizationFunctor P S).EssSurj := sorry

/-- Stacks 0GSL: a left denominator cover makes the localized inclusion essentially
surjective. -/
@[stacks 0GSL "localized essential surjectivity from right resolutions"]
theorem essSurj_of_rightResolutions
    [(fullSubcategoryLocalizerMorphism P S).HasRightResolutions] :
    (fullSubcategoryLocalizationFunctor P S).EssSurj := sorry

end fullSubcategoryLocalizationFunctor.cover

namespace fullSubcategoryLocalizerMorphism.cover

/-- Stacks 0GSL: the inclusion-induced localizer morphism is a localized equivalence under a
right denominator cover. -/
@[stacks 0GSL]
instance isLocalizedEquivalence [IsSaturatedMultiplicativeSystem S]
    [(fullSubcategoryLocalizerMorphism P S).HasLeftResolutions] :
    (fullSubcategoryLocalizerMorphism P S).IsLocalizedEquivalence := sorry

/-- Stacks 0GSL: the inclusion-induced localizer morphism is a localized equivalence under a
left denominator cover. -/
@[stacks 0GSL "localized full-subcategory equivalence from right resolutions"]
instance isLocalizedEquivalence_of_rightResolutions
    [IsSaturatedMultiplicativeSystem S]
    [(fullSubcategoryLocalizerMorphism P S).HasRightResolutions] :
    (fullSubcategoryLocalizerMorphism P S).IsLocalizedEquivalence := sorry

end fullSubcategoryLocalizerMorphism.cover


end CategoryTheory
