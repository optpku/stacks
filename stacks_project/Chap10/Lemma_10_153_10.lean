/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.KrullDimension
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.153.10

@stack 06RS

Zero-dimensional local rings are henselian.
-/

@[stacks 06RS "zero-dimensional local rings are henselian"]
#check @HenselianLocalRing.of_krullDimLE_zero
