/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Depth.FiniteAlgebra
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.72.11

@stack 0AUK
-/

/- Chap10 Lemma 10 72 11: depth over a Noetherian local base is the infimum
of the depths at the maximal ideals of a finite algebra. -/
@[stacks 0AUK]
#check @Module.moduleDepth_eq_iInf_atMaximal
