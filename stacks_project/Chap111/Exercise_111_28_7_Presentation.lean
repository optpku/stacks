/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.HilbertFunction

/-!
# Residue-field Hilbert function of an associated graded local ring

This leaf preserves the source-facing type of the local Hilbert function while
the reusable declarations live in its mathematical owner.
-/

@[expose] public section

universe u

namespace IsLocalRing

variable {A : Type u}

/- The compatibility surface retains the complete Hilbert-function type. -/
#check (associatedGradedHilbertFn :
  (A : Type u) → [CommRing A] → [IsLocalRing A] → ℕ → ℕ)

end IsLocalRing
