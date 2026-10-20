/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Gorenstein.Ring
public import ReasLib.RingTheory.CohenMacaulay.Ring

@[expose] public section

universe u

namespace IsGorensteinRing

/-- Every Gorenstein commutative ring is Cohen-Macaulay. -/
instance instCohenMacaulayRing
    (R : Type u) [CommRing R] [IsGorensteinRing R] :
    CohenMacaulayRing R := sorry

end IsGorensteinRing
