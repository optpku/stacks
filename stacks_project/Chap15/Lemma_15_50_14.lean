/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Regular.GRing
import StacksCheckRecall

/-!
# Lemma 15.50.14

@stack 0AH2
-/

@[expose] public section

/- Lemma 15.50.14: the reusable G-ring completion bridge is owned by
`IsGRing.AdicCompletion.regularMap`. -/
@[stacks 0AH2]
#check @IsGRing.AdicCompletion.regularMap
