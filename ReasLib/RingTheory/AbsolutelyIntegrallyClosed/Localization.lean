/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.Basic
public import ReasLib.RingTheory.AbsolutelyIntegrallyClosed

@[expose] public section

/-!
# Localizations of absolutely integrally closed rings

The explicit theorem supports arbitrary models of a localization. The instance is
reserved for Mathlib's canonical `Localization` type.

@stack 0DCN
-/

universe u v

namespace IsAbsolutelyIntegrallyClosed

/-- Any localization model of an absolutely integrally closed ring is absolutely
integrally closed. -/
@[stacks 0DCN "absolute integral closedness of localization models"]
theorem of_isLocalization {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] [IsAbsolutelyIntegrallyClosed A] (M : Submonoid A)
    [IsLocalization M B] : IsAbsolutelyIntegrallyClosed B := sorry
-- Proof strategy: clear denominators with `IsLocalization.scaleRoots_commonDenom_mem_lifts`,
-- recover a monic lift using `Polynomial.lifts_and_natDegree_eq_and_monic`, split it over `A`,
-- and undo `Polynomial.scaleRoots` by the localized denominator unit.

/-- The canonical localization of an absolutely integrally closed ring is
absolutely integrally closed. -/
@[stacks 0DCN "absolute integral closedness of canonical localizations"]
instance localization {A : Type u} [CommRing A] [IsAbsolutelyIntegrallyClosed A]
    (M : Submonoid A) : IsAbsolutelyIntegrallyClosed (Localization M) := sorry
-- Proof strategy: instantiate `of_isLocalization` with Mathlib's canonical `Localization`
-- model and its `IsLocalization` instance.

end IsAbsolutelyIntegrallyClosed
