/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Regular.CohenMacaulay
import StacksCheckRecall

/-!
# Lemma 15.42.4 (0H7T)

@stack 0H7T
-/

@[expose] public section

/- Lemma 15.42.4 (0H7T): Cohen-Macaulayness ascends along a regular ring map with Noetherian
target. -/
@[stacks 0H7T]
#check @RingHom.Regular.cohenMacaulayRing
