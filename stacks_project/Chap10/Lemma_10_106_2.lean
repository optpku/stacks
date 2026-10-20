/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RegularLocalRing.Domain
import StacksCheckRecall

/-!
# Lemma 10.106.2

@stack 00NP
-/

@[expose] public section

/- Lemma 10.106.2 [stacks 00NP]: the reusable domain instance for regular
local rings. -/
@[stacks 00NP]
#check @IsRegularLocalRing.isDomain
