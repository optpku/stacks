/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Sequence.QuasiRegular.BaseChange
import StacksCheckRecall

/-!
# Flat base change of a quasi-regular sequence

@stack 065L
-/

@[expose] public section

/- Lemma 10.69.3 (065L): a quasi-regular sequence remains quasi-regular after
flat scalar extension. This is the canonical tensor-product owner. -/
@[stacks 065L "flat base change"]
#check @RingTheory.Sequence.IsQuasiRegular.of_flat
