/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.FaithfullyFlat.Normal
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.164.3

@stack 033G
-/

/- Lemma 10.164.3 [stacks 033G]: canonical recall of normality descent along
a faithfully flat ring homomorphism. -/
@[stacks 033G]
#check @RingHom.FaithfullyFlat.isNormalRing
