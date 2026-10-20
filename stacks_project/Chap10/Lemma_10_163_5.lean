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
# Lemma 10.163.5

@stack 033A
-/

/- Lemma 10.163.5 [stacks 033A]: canonical recall of `(R_k)` ascent along a flat
algebra with fiberwise `(R_k)`. -/
@[stacks 033A]
#check @Algebra.Fiber.serreConditionR_of_flat
