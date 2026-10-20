/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.FormalFiber.PRing.Completion
import StacksCheckRecall

/-!
# Lemma 15.51.6

@stack 0BK9
-/

@[expose] public section

/- Lemma 15.51.6: every fiber of an adic completion of a `P`-ring has `P` when `P` satisfies
locality and faithfully-flat descent. -/
@[stacks 0BK9 "adic-completion fibers of a P-ring"]
#check @IsPRing.adicCompletionFiber
