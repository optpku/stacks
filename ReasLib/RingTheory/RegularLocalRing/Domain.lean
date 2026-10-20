/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regular Local Rings Are Domains

Regular local rings are integral domains.
-/

@[expose] public section

universe u

namespace IsRegularLocalRing

/-- A regular local ring is an integral domain. -/
@[stacks 00NP "regular local rings are domains"]
instance isDomain {R : Type u} [CommRing R] [IsRegularLocalRing R] :
    IsDomain R := sorry

end IsRegularLocalRing
