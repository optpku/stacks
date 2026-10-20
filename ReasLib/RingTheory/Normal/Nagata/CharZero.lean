/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Nagata

@[expose] public section

/-!
# Japanese Domains in Characteristic Zero

@stack 032M

This leaf identifies the `N-1` and `N-2` conditions for Noetherian domains
whose fraction field has characteristic zero.
-/

universe u

namespace IsN1Ring

/-- Lemma 10.161.11, tag `032M`: for a Noetherian domain whose fraction field
has characteristic zero, the `N-1` and `N-2` conditions are equivalent. -/
@[stacks 032M]
theorem iff_isN2Ring_of_fractionRingCharZero
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CharZero (FractionRing R)] :
    IsN1Ring R ↔ IsN2Ring R := sorry

end IsN1Ring
