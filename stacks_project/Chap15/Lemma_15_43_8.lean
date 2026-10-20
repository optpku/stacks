/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.LocalMap.Flat
import StacksCheckRecall

/-!
Lemma 15.43.8 (0C4G): Let `A → B` be a local homomorphism of Noetherian local rings.
The induced map of maximal-ideal completions is flat if and only if `A → B` is flat.

The completion map and its flatness criterion are owned by ReasLib.

@stack 0C4G
-/

@[expose] public section

/- Lemma 15.43.8: flatness of the induced maximal-ideal completion map is equivalent to flatness
of the original local homomorphism. -/
@[stacks 0C4G "flatness and maximal-ideal completion"]
#check @AdicCompletion.mapLocal_flat_iff

@[stacks 0C4G "canonical completion map"]
#check @AdicCompletion.mapLocal

@[stacks 0C4G "completion map composition"]
#check @AdicCompletion.mapLocal_comp

#print axioms AdicCompletion.mapLocal
