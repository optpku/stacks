/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.Regular.GRing
import Mathlib.Tactic.CrossRefAttribute

/-!
# Complete local G-rings

@stack 07PS

This leaf is independent of the alternative formal-fiber characterization of G-rings.
-/

@[expose] public section

universe u

namespace IsGRing

/-- Proposition 15.50.6: every Noetherian complete local ring is a G-ring. -/
@[stacks 07PS "complete local rings are G-rings",
  stacks 07PX "Proposition 15.50.12 (2)"]
instance completeLocal (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsCompleteLocalRing R] : IsGRing R := sorry

end IsGRing
