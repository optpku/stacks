/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.FaithfullyFlat.Serre
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.164.5

@stack 0352
-/

/- Lemma 10.164.5 [stacks 0352]: canonical recall of faithfully flat descent
for Serre's condition `(S_k)`. -/
@[stacks 0352]
#check @RingHom.FaithfullyFlat.serreConditionS
