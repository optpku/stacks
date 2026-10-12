/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Localizing ring pullback squares away from an element

@stack 01Z8

A cartesian square of commutative rings remains cartesian after localizing all four rings away
from the images of one element of the pullback ring.
-/

open CategoryTheory.Limits CommRingCat
open IsLocalization.Away

universe u

namespace CategoryTheory.IsPullback

section RightMap

variable {R R' B B' Rf Rh : Type u}
variable [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
variable [CommRing Rf] [CommRing Rh]
variable {s : B →+* R} {t : R' →+* R} {left : B' →+* B} {right : B' →+* R'}
variable [Algebra R' Rf] [Algebra R Rh]

/-- The pullback relation identifies the two elements used to localize the common target. -/
@[stacks 01Z8 "common target localization"]
theorem awayRight (h : B')
    [IsLocalization.Away (s (left h)) Rh]
    (hsq : IsPullback (ofHom left) (ofHom right) (ofHom s) (ofHom t)) :
    IsLocalization.Away (t (right h)) Rh := by
  rw [show t (right h) = s (left h) by
    exact (ConcreteCategory.congr_hom hsq.w h).symm]
  infer_instance

/-- The canonical map from the localization of `R'` to the localization of `R` induced by a
pullback square. -/
@[stacks 01Z8 "localized right comparison map"]
noncomputable def localizationAwayRightMap (h : B')
    [IsLocalization.Away (right h) Rf] [IsLocalization.Away (s (left h)) Rh]
    (hsq : IsPullback (ofHom left) (ofHom right) (ofHom s) (ofHom t)) :
    Rf →+* Rh :=
  -- Local instance justification (proof-local temporary data): the pullback relation identifies
  -- the two target denominators, selecting the target localization structure required by `map`.
  letI : IsLocalization.Away (t (right h)) Rh := awayRight h hsq
  IsLocalization.Away.map Rf Rh t (right h)

/-- The localized right comparison map sends a base element through the original ring map. -/
@[simp, stacks 01Z8 "localized right comparison map on generators"]
theorem localizationAwayRightMap_algebraMap_apply (h : B')
    [IsLocalization.Away (right h) Rf] [IsLocalization.Away (s (left h)) Rh]
    (hsq : IsPullback (ofHom left) (ofHom right) (ofHom s) (ofHom t)) (x : R') :
    localizationAwayRightMap h hsq (algebraMap R' Rf x) = algebraMap R Rh (t x) := sorry

end RightMap

section Square

variable {R R' B B' Bg Rf Bh Rh : Type u}
variable [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
variable [CommRing Bg] [CommRing Rf] [CommRing Bh] [CommRing Rh]
variable {s : B →+* R} {t : R' →+* R} {left : B' →+* B} {right : B' →+* R'}
variable [Algebra B Bg] [Algebra R' Rf] [Algebra B' Bh] [Algebra R Rh]

/-- Localizing a cartesian square of commutative rings away from the images of an element of its
pullback ring gives another cartesian square. -/
@[stacks 01Z8 "localization away preserves ring pullbacks"]
theorem localizationAway (h : B')
    [IsLocalization.Away (left h) Bg] [IsLocalization.Away (right h) Rf]
    [IsLocalization.Away h Bh] [IsLocalization.Away (s (left h)) Rh]
    (hsq : IsPullback (ofHom left) (ofHom right) (ofHom s) (ofHom t)) :
    IsPullback (ofHom (IsLocalization.Away.map Bh Bg left h))
      (ofHom (IsLocalization.Away.map Bh Rf right h))
      (ofHom (IsLocalization.Away.map Bg Rh s (left h)))
      (ofHom (localizationAwayRightMap h hsq)) := sorry

end Square

end CategoryTheory.IsPullback
