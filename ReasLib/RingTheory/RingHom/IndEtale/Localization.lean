/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.RingTheory.RingHom.IndEtale.Basic

@[expose] public section

/-!
# Localizations of ind-etale ring maps

This leaf provides ind-etale constructors for arbitrary localizations and
their common away-localization specialization, without exposing a chosen
filtered presentation.

@stack 04GV
-/

universe u v w

namespace RingHom.IndEtale

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- A localization at an arbitrary submonoid is ind-etale over its source ring. -/
theorem of_isLocalization (M : Submonoid R) [IsLocalization M A] :
    (algebraMap R A).IndEtale := sorry

end RingHom.IndEtale

namespace RingHom.IndEtale.Raw

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- A localization at an arbitrary submonoid has an ind-etale presentation at any
presentation universe. -/
theorem of_isLocalization (M : Submonoid R) [IsLocalization M A] :
    RingHom.IndEtale.Raw.{u, v, w} (algebraMap R A) := sorry

end RingHom.IndEtale.Raw

namespace RingHom.IndEtale

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- An away localization is ind-etale over its source ring. -/
theorem of_isLocalizationAway (r : R) [IsLocalization.Away r A] :
    (algebraMap R A).IndEtale := sorry

end RingHom.IndEtale

namespace RingHom.IndEtale.Raw

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- An away localization has an arbitrary-size ind-etale presentation. -/
theorem of_isLocalizationAway (r : R) [IsLocalization.Away r A] :
    RingHom.IndEtale.Raw.{u, v, w} (algebraMap R A) := sorry

end RingHom.IndEtale.Raw
