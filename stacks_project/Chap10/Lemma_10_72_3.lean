/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Depth.SupportDim
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.72.3

@stack 00LK

The local depth bound is recalled directly from the reusable support-dimension API.
-/

/- Lemma 10.72.3: local module depth is bounded by support dimension. -/
@[stacks 00LK]
#check @Module.depth_le_supportDim
