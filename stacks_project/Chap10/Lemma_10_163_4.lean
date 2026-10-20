/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flat.Fiber.Serre
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.163.4

@stack 0339
-/

/- Lemma 10.163.4 [stacks 0339]: canonical recall of `(S_k)` ascent along a flat
algebra with fiberwise `(S_k)`. -/
@[stacks 0339]
#check @Algebra.Fiber.serreConditionS_of_flat
