/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Regular.GRing.CompleteLocal
import StacksCheckRecall

/-!
# Proposition 15.50.6

@stack 07PS
-/

@[expose] public section

/- Proposition 15.50.6, tag `07PS`: every Noetherian complete local ring is a G-ring. -/
@[stacks 07PS "complete local rings are G-rings"]
#check @IsGRing.completeLocal
