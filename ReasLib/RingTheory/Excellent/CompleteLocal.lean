/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Catenary.CompleteLocal
public import ReasLib.RingTheory.Excellent
public import ReasLib.RingTheory.Regular.GRing.CompleteLocal
public import ReasLib.RingTheory.Regular.JRing.CompleteLocal

@[expose] public section

/-!
# Complete Local Excellent Rings

@stack 07QW
-/

universe u v

namespace IsExcellentRing

/-- Every Noetherian complete local ring is excellent. -/
@[stacks 07QW "complete local rings are excellent"]
instance completeLocal
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R] :
    IsExcellentRing.{u, v} R := sorry

end IsExcellentRing
