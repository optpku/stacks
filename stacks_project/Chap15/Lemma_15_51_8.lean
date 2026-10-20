/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.FormalFiber.PRing.Henselization
import StacksCheckRecall

/-!
# Lemma 15.51.8

@stack 0C36
-/

@[expose] public section

/- Lemma 15.51.8 (1): a henselization of a local `P`-ring is a `P`-ring. -/
@[stacks 0C36 "(1)"]
#check @IsHenselizationOf.isPRing

/- Lemma 15.51.8 (2): a strict henselization of a local `P`-ring is a `P`-ring. -/
@[stacks 0C36 "(2)"]
#check @IsStrictHenselizationOf.isPRing
