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
# Lemma 10.163.2

@stack 0337
-/

/- Lemma 10.163.2 [stacks 0337]: canonical recall of the closed-fiber depth formula
for a flat local homomorphism. -/
@[stacks 0337]
#check @Algebra.Fiber.moduleDepth_target_eq_add_closed
