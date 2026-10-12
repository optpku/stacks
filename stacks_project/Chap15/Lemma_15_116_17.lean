/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.Complete
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.116.17

The complete-DVR existence theorem is owned by IsWeakSolutionFor.exists_of_complete. This
source-facing file retains the exact Stacks label and checks the reusable statement without
importing Chapter 10 or proof-only normalization helpers.

@stack 09F8
-/

@[stacks 09F8 "Lemma 15.116.17: complete weak-solution existence"]
#check @IsWeakSolutionFor.exists_of_complete
#check @IsExtensionOfDiscreteValuationRings.of_tower
#check @IsWeakSolutionFor
