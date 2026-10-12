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
# Lemma 10.164.6

@stack 0353
-/

/- Lemma 10.164.6 [stacks 0353]: canonical recall of faithfully flat descent
for Serre's condition `(R_k)`. -/
@[stacks 0353]
#check @RingHom.FaithfullyFlat.serreConditionR
