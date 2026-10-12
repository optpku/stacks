/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Completion.Henselian
import StacksCheckRecall

@[expose] public section

universe u

/- Theorem 59.32.3: Complete local rings are henselian. -/
@[stacks 03QG] #check (IsCompleteLocalRing.henselianLocalRing :
    ∀ {R : Type u} [CommRing R] [IsCompleteLocalRing R], HenselianLocalRing R)
