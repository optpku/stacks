/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.FormalFiber.PRing.PairHenselization
import StacksCheckRecall

/-!
# Lemma 15.51.7

@stack 0BKA
-/

@[expose] public section

/- Lemma 15.51.7: a henselization of a pair over a `P`-ring is a `P`-ring when `P` satisfies
locality, regular ascent, faithfully-flat descent, and separable extension. -/
@[stacks 0BKA "pair henselizations of P-rings"]
#check @IsPairHenselization.isPRing
