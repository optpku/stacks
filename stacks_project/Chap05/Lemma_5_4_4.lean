/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.SeparatedMap
import StacksCheckRecall

@[expose] public section

/- Canonical core: fiberwise separation is preserved by pullback without continuity assumptions. -/
@[stacks 0CY4 "separatedness is preserved by pullback"]
#check IsSeparatedMap.pullback
