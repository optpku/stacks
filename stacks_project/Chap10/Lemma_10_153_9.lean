/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Completion.Henselian
import StacksCheckRecall

@[expose] public section

/-!
# Complete local rings are henselian

@stack 04GM

Lemma 10.153.9 is a source-facing recall of the neutral instance
`IsCompleteLocalRing.henselianLocalRing`, which specializes Mathlib's
`IsAdicComplete.henselianRing` at the maximal ideal.
-/

/- Lemma 10.153.9 (Stacks tag `04GM`): a local ring complete for the
maximal-ideal adic topology is henselian. -/
@[stacks 04GM]
#check @IsCompleteLocalRing.henselianLocalRing
#print axioms IsCompleteLocalRing.henselianLocalRing
