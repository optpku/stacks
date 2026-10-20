/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.Length.Annihilator
import StacksCheckRecall

@[expose] public section

/-!
# Length over a local ring

@stack 00IW

The finite-length annihilator statement is owned by
`Module.exists_pow_maximalIdeal_smul_top_eq_bot_of_isFiniteLength`.
-/

/- Lemma 10.52.4: a finite-length module over a local ring is annihilated by a power of the
maximal ideal. -/
@[stacks 00IW "finite-length annihilator"]
#check @Module.exists_pow_maximalIdeal_smul_top_eq_bot_of_isFiniteLength
