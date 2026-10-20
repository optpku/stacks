/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Over

/-!
# Integral compatibility facade for K-injective localization

The canonical owner is `CochainComplex.Enriched.Over.KInjective`, whose explicit base-ring
parameter makes the model reusable for every linear enrichment.  The declarations below retain
the historical integral namespace while delegating all data and instances to that owner.
-/

@[expose] public section

noncomputable section

universe u v w g

open CategoryTheory CategoryTheory.Limits DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped CategoryTheory.CochainComplex.Enriched.Over

namespace CategoryTheory.CochainComplex.Enriched.KInjective

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The historical integral K-injective object property. -/
@[stacks 0CS6 "integral K-injective objects"]
abbrev property : ObjectProperty (DifferentialGradedCategory.K ℤ (CochainComplex C ℤ)) :=
  Over.KInjective.property (R := ℤ) (C := C)

/-- Compatibility characterization of integral K-injectivity. -/
@[simp]
theorem property_iff (K : DifferentialGradedCategory.K ℤ (CochainComplex C ℤ)) :
    property (C := C) K ↔ K.obj.IsKInjective := sorry

/-- Compatibility theorem exposing the K-injectivity proof on a model object.
The generic owner supplies the actual typeclass instance. -/
@[stacks 0CS6 "integral K-injective model instance"]
theorem fullSubcategoryIsKInjective
    (I : (property (C := C)).FullSubcategory) : I.obj.obj.IsKInjective := sorry

/-- The historical integral denominator system on K-injective models. -/
abbrev qis : MorphismProperty (property (C := C)).FullSubcategory :=
  Over.KInjective.qis (R := ℤ) (C := C)

/-- The historical integral K-injective localization. -/
noncomputable abbrev localization [HasDerivedCategory.{w} C] :
    (property (C := C)).FullSubcategory ⥤ DerivedCategory.{w} C :=
  Over.KInjective.localization (R := ℤ) (C := C)

/-- Compatibility characterization of the integral localization. -/
@[stacks 0CS6 "integral K-injective localization"]
theorem localizationIsLocalization [HasDerivedCategory.{w} C]
    [IsGrothendieckAbelian.{g} C] :
    (localization (C := C)).IsLocalization (qis (C := C)) := sorry

/-- The historical integral functorial K-injective resolution object. -/
noncomputable abbrev resolutionObject
    (R : CochainComplex.KInjectiveResolution.Functorial C)
    (X : DifferentialGradedCategory.K ℤ (CochainComplex C ℤ)) :
    (property (C := C)).FullSubcategory :=
  Over.KInjective.resolutionObject (R := ℤ) (C := C) R X

/-- The historical integral functorial resolution arrow. -/
noncomputable abbrev resolutionMap
    (R : CochainComplex.KInjectiveResolution.Functorial C)
    (X : DifferentialGradedCategory.K ℤ (CochainComplex C ℤ)) :
    X ⟶ (property (C := C)).ι.obj (resolutionObject (C := C) R X) :=
  Over.KInjective.resolutionMap (R := ℤ) (C := C) R X

/-- The historical integral right denominator resolution. -/
noncomputable abbrev rightResolutionOf
    (R : CochainComplex.KInjectiveResolution.Functorial C)
    (X : DifferentialGradedCategory.K ℤ (CochainComplex C ℤ)) :=
  Over.KInjective.rightResolutionOf (R := ℤ) (C := C) R X

/-- Compatibility theorem for the right-resolution cover. -/
@[stacks 090Y "integral K-injective right-resolution cover"]
theorem hasRightResolutions_of_grothendieck
    [IsGrothendieckAbelian.{g} C] :
    (fullSubcategoryLocalizerMorphism (property (C := C))
      (CochainComplex.Enriched.quasiIso (A := C))).HasRightResolutions := sorry

/-- Compatibility theorem for the localized-equivalence presentation. -/
@[stacks 0CS6 "integral K-injective localized equivalence"]
theorem localizerIsLocalizedEquivalence [IsGrothendieckAbelian.{g} C] :
    (fullSubcategoryLocalizerMorphism (property (C := C))
      (CochainComplex.Enriched.quasiIso (A := C))).IsLocalizedEquivalence := sorry

end CategoryTheory.CochainComplex.Enriched.KInjective
