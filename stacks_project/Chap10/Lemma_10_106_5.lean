/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.FreeLifting
import StacksCheckRecall

@[expose] public section

/-!
# Freeness across a regular principal quotient

@stack 00NS
-/

/- Lemma 10.106.5: a regular element in the maximal ideal lifts freeness from the
principal quotient of a finite module over a Noetherian local ring. -/
@[stacks 00NS]
#check @Module.Free.LocalRing.of_regular_quotient
