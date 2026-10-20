/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flat.Fiber.Normal
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.163.8

@stack 0C22
-/

/- Lemma 10.163.8 [stacks 0C22]: canonical recall of normality ascent along a
flat algebra with normal residue-field fibers. -/
@[stacks 0C22]
#check @Algebra.Fiber.isNormalRing_of_flat
