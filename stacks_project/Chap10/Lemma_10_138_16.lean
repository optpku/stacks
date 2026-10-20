/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Smooth.Descent
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.138.16

@stack 06CM
-/

/- Lemma 10.138.16 [stacks 06CM]: canonical recall of faithfully flat descent
and base change for formal smoothness. -/
@[stacks 06CM]
#check @Algebra.FormallySmooth.iff_tensorProduct_of_faithfullyFlat
