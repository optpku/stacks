/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.GenericPoints
public import ReasLib.RingTheory.Localization.BasicOpen

/-!
# Birational Localization Morphisms

This module records birationality and a principal-open obstruction for the
spectrum morphism induced by localization at an arbitrary submonoid.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LocalizationMorphism

noncomputable section

/-- The spectrum morphism induced by the localization map `A → Localization S`. -/
abbrev hom (A : Type u) [CommRing A] (S : Submonoid A) :
    Spec (CommRingCat.of (Localization S)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Localization S)))

/-- Localization at a submonoid avoiding zero induces a birational morphism of spectra of a
domain. -/
theorem isBirational (A : Type u) [CommRing A] [IsDomain A]
    (S : Submonoid A) (h0 : (0 : A) ∉ S) :
    AlgebraicGeometry.IsBirational (hom A S) := sorry

/-- If a localization morphism is an isomorphism over a nonempty open of the target, then all
elements of the localized submonoid become units in one principal localization. -/
theorem exists_away_isUnit_of_exists_isIso_restrict
    (A : Type u) [CommRing A] [IsDomain A] (S : Submonoid A) (h0 : (0 : A) ∉ S)
    (hU : ∃ U : (Spec (CommRingCat.of A)).Opens, Nonempty U ∧ IsIso (hom A S ∣_ U)) :
    ∃ a : A, ∀ s : S, IsUnit (algebraMap A (Localization.Away a) s.1) := sorry

end

end AlgebraicGeometry.LocalizationMorphism
