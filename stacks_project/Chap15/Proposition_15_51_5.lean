/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.FormalFiber.EssFiniteType
import StacksCheckRecall

/-!
# Proposition 15.51.5

@stack 0BIV
-/

@[expose] public section

/- Proposition 15.51.5, tag `0BIV`: an essentially finite type algebra over a `P`-ring is a
`P`-ring when `P` satisfies the four base-change, locality, ascent, and descent laws. -/
@[stacks 0BIV "essentially finite type extension of a P-ring"]
#check @IsPRing.of_essFiniteType
