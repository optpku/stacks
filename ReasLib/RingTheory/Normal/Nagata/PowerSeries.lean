/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Nagata
public import ReasLib.RingTheory.PowerSeries.Finite

@[expose] public section

/-!
# Japanese Power Series Rings

This module records permanence of the `N-2` condition under adjoining one
formal power-series variable.
-/

universe u

open scoped PowerSeries

namespace IsN2Ring

variable {R : Type u}

/-- Lemma 10.161.17, tag `032Q`: a one-variable formal power-series ring over a
Noetherian `N-2` domain is `N-2`. -/
@[stacks 032Q]
theorem powerSeries [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsN2Ring R] :
    IsN2Ring R⟦X⟧ := sorry

end IsN2Ring
