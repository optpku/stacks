/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Smooth.IntegralClosure
import StacksCheckRecall

/-!
# Lemma 10.147.2

@stack 03GE

The smooth base-change theorem is stronger than the source's etale
specialization.
-/

@[expose] public section

@[stacks 03GE "integral closure under smooth base change"]
#check @TensorProduct.toIntegralClosure_bijective_of_smooth
