/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom

@[expose] public section

namespace RingHom.IsLocalCompleteIntersection

/-- Local complete-intersection ring maps are stable under composition. -/
theorem stableUnderComposition :
    RingHom.StableUnderComposition (@RingHom.IsLocalCompleteIntersection) := sorry

end RingHom.IsLocalCompleteIntersection
