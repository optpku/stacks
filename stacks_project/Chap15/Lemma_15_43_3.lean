/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Completion.CohenMacaulay
import StacksCheckRecall

/-!
# Lemma 15.43.3 (07NX)

@stack 07NX
-/

@[expose] public section

/- Lemma 15.43.3 (07NX): Cohen-Macaulayness is preserved and reflected by maximal-ideal
completion. -/
@[stacks 07NX]
#check @AdicCompletion.cohenMacaulay_iff
