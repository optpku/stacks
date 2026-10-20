/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Regular.GRing
import StacksCheckRecall

/-!
# Lemma 15.50.14

@stack 0AH2
-/

@[expose] public section

/- Lemma 15.50.14: the reusable G-ring completion bridge is owned by
`IsGRing.AdicCompletion.regularMap`. -/
@[stacks 0AH2]
#check @IsGRing.AdicCompletion.regularMap
