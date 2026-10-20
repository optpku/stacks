/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flat.Fiber.CohenMacaulay
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.163.3

@stack 045J
-/

/- Lemma 10.163.3 [stacks 045J]: canonical recall of the Cohen--Macaulay
criterion for a flat local homomorphism and its closed fiber. -/
@[stacks 045J]
#check @Algebra.Fiber.cohenMacaulayRing_iff_source_and_closed
