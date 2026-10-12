/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Catenary.Universally
public import ReasLib.RingTheory.Completion.LocalRing

/-!
# Universal catenarity of complete local rings

@stack 032C
-/

@[expose] public section

universe u v

namespace UniversallyCatenaryRing

/-- Remark 10.160.9 (Stacks `032C`): every Noetherian complete local ring is universally
catenary. -/
@[stacks 032C]
instance completeLocal (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsCompleteLocalRing R] : UniversallyCatenaryRing.{u, v} R := sorry

end UniversallyCatenaryRing
