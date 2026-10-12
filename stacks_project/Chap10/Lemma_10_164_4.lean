/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.FaithfullyFlat.Regular
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.164.4

@stack 07NG
-/

/- Lemma 10.164.4 [stacks 07NG]: canonical recall of regularity descent along
a faithfully flat ring homomorphism. -/
@[stacks 07NG]
#check @RingHom.FaithfullyFlat.isRegularRing
