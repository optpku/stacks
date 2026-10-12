/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.RingTheory.Gorenstein.CohenMacaulay
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 47.21.2: A Gorenstein ring is Cohen-Macaulay. -/
@[stacks 0DW8] #check
  (IsGorensteinRing.instCohenMacaulayRing :
    ∀ (R : Type u) [CommRing R] [IsGorensteinRing R], CohenMacaulayRing R)
