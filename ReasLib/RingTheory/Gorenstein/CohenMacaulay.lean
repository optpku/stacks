/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
