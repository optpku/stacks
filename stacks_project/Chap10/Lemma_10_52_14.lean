/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.Length.Fiber
import StacksCheckRecall

@[expose] public section

/-!
# Multiplicativity of closed-fiber lengths

The statement is the composite-map consequence of the flat local base-change
length formula in `IsLocalRing.length_baseChange_eq_mul_fiber`.

@stack 02M2
-/

/- Lemma 10.52.14: for flat local homomorphisms `A ⟶ B ⟶ C`, closed-fiber lengths multiply
under composition. -/
@[stacks 02M2 "closed-fiber length multiplicativity"]
#check @IsLocalRing.length_fiber_mul_fiber_eq_composite
