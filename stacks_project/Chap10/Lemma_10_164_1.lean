/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.FaithfullyFlat.Noetherian
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.164.1

@stack 033E
-/

/- Lemma 10.164.1 [stacks 033E]: canonical recall of Noetherian descent along
a faithfully flat ring homomorphism. -/
@[stacks 033E]
#check @RingHom.FaithfullyFlat.isNoetherianRing
