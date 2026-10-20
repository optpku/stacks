/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.HilbertFunction

@[expose] public section

universe u

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- If the first three values of the residue-field Hilbert function are
`1`, `3`, and `5`, then its value in degree three is at most `7`. -/
theorem associatedGradedHilbertFn_three_le
    (h0 : associatedGradedHilbertFn R 0 = 1)
    (h1 : associatedGradedHilbertFn R 1 = 3)
    (h2 : associatedGradedHilbertFn R 2 = 5) :
    associatedGradedHilbertFn R 3 ≤ 7 := by
  sorry

end IsLocalRing
