/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Module.Support.FiniteLength
import StacksCheckRecall

@[expose] public section

/-!
# Finite length and support over a local ring

@stack 00L5
-/

/- Lemma 10.62.3: a nonzero finite module over a Noetherian local ring has support equal to the
closed point exactly when it has finite length. -/
@[stacks 00L5]
#check @Module.support_eq_singleton_closedPoint_iff_isFiniteLength
