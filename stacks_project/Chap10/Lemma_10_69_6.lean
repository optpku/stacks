/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Sequence.QuasiRegular.MaximalIdeal
import StacksCheckRecall

/-!
# Quasi-regular sequences in the maximal ideal

@stack 061S
-/

@[expose] public section

universe u v

/- The source item is a canonical recall; the owner carries the declaration and tag. -/
@[stacks 061S]
#check @RingTheory.Sequence.IsQuasiRegular.isRegular_of_mem_maximalIdeal
