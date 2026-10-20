/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Nagata

@[expose] public section

/-!
# Localization of N-1 and N-2 Domains

This module records localization permanence for the `N-1` and `N-2`
conditions on domains.

@stack 032H
-/

universe u v

namespace IsN1Ring

/-- Lemma 10.161.3 (1), tag `032G`: a localization of an `N-1` domain that is a domain is
again `N-1`. -/
@[stacks 032G "(1)"]
theorem of_isLocalization {R : Type u} {Rₘ : Type v}
    [CommRing R] [IsDomain R] [CommRing Rₘ] [Algebra R Rₘ] [IsDomain Rₘ]
    (M : Submonoid R) [IsLocalization M Rₘ] [IsN1Ring R] :
    IsN1Ring Rₘ := sorry

end IsN1Ring

namespace IsN2Ring

/-- Lemma 10.161.3 (2), tag `032G`: a localization of an `N-2` domain that is a domain is
again `N-2`. -/
@[stacks 032G "(2)"]
theorem of_isLocalization {R : Type u} {Rₘ : Type v}
    [CommRing R] [IsDomain R] [CommRing Rₘ] [Algebra R Rₘ] [IsDomain Rₘ]
    (M : Submonoid R) [IsLocalization M Rₘ] [IsN2Ring R] :
    IsN2Ring Rₘ := sorry

end IsN2Ring

namespace IsN1Ring

/-- Lemma 10.161.4 (1), tag `032H`: an `N-1` condition on a finite family of
principal localizations whose generators span the unit ideal descends to the base domain. -/
@[stacks 032H "(1)"]
theorem of_localizationSpan {R : Type u} [CommRing R] [IsDomain R]
    (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤)
    (hdom : ∀ f : s, IsDomain (Localization.Away f.1))
    (h : ∀ f : s, IsN1Ring (Localization.Away f.1)) :
    IsN1Ring R := sorry

end IsN1Ring

namespace IsN2Ring

/-- Lemma 10.161.4 (2), tag `032H`: an `N-2` condition on a finite family of
principal localizations whose generators span the unit ideal descends to the base domain. -/
@[stacks 032H "(2)"]
theorem of_localizationSpan {R : Type u} [CommRing R] [IsDomain R]
    (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤)
    (hdom : ∀ f : s, IsDomain (Localization.Away f.1))
    (h : ∀ f : s, @IsN2Ring (Localization.Away f.1) _ (hdom f)) :
    IsN2Ring R := sorry

end IsN2Ring
