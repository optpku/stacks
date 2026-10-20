/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import ReasLib.RingTheory.AbsolutelyIntegrallyClosed.Localization
public import ReasLib.RingTheory.Henselian.StrictHenselian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Strict henselianity of absolutely integrally closed localizations

The canonical instance is stated for an arbitrary local absolutely integrally closed ring.  The
source-facing localization theorem then follows by combining it with the canonical localization
owner for absolute integral closedness.

@stack 0DCS
-/

@[expose] public section

open IsLocalRing

universe u

namespace IsAbsolutelyIntegrallyClosed

/-- A local absolutely integrally closed ring is strictly henselian. -/
@[stacks 0DCS "strict henselianity of local absolutely integrally closed rings"]
instance strictHenselianLocalRing
    {A : Type u} [CommRing A] [IsLocalRing A] [IsAbsolutelyIntegrallyClosed A] :
    StrictHenselianLocalRing A := sorry

/-- Lemma 15.14.7: the localization of an absolutely integrally closed ring at a prime ideal is
strictly henselian. -/
@[stacks 0DCS "strict henselianity after localization at a prime"]
theorem localizationAtPrime_strictHenselian
    {A : Type u} [CommRing A] [IsAbsolutelyIntegrallyClosed A]
    (p : Ideal A) [p.IsPrime] :
    StrictHenselianLocalRing (Localization.AtPrime p) := sorry

end IsAbsolutelyIntegrallyClosed
