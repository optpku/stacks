/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom

@[expose] public section

namespace RingHom.IsLocalCompleteIntersection

/-- Local complete-intersection ring maps are stable under composition. -/
theorem stableUnderComposition :
    RingHom.StableUnderComposition (@RingHom.IsLocalCompleteIntersection) := sorry

end RingHom.IsLocalCompleteIntersection
