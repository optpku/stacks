/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flat.Fiber.Depth
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.163.1

@stack 0338
-/

/- Lemma 10.163.1 [stacks 0338]: canonical recall of depth additivity for finite
modules along a flat local homomorphism. -/
@[stacks 0338]
#check @Algebra.Fiber.moduleDepth_tensor_eq_add_closed
