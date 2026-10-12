/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.RingTheory.LocalRing.HilbertFunction.Bounds
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.58.8 -/
@[stacks 0D5N] #check (IsLocalRing.associatedGradedHilbertFn_three_le :
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
    IsLocalRing.associatedGradedHilbertFn R 0 = 1 →
    IsLocalRing.associatedGradedHilbertFn R 1 = 3 →
    IsLocalRing.associatedGradedHilbertFn R 2 = 5 →
    IsLocalRing.associatedGradedHilbertFn R 3 ≤ 7)
