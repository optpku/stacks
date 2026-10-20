/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flat.Fiber.Reduced
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.163.6

@stack 0C21
-/

/- Lemma 10.163.6 [stacks 0C21]: canonical recall of reducedness ascent along a
flat algebra with reduced residue-field fibers. -/
@[stacks 0C21]
#check @Algebra.Fiber.isReduced_of_flat
