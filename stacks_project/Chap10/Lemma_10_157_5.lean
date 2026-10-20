/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Normal.Regular
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.157.5

@stack 0567

The source statement is exactly the shared regular-to-normal theorem.
-/

@[stacks 0567]
#check @IsRegularRing.isNormalRing
