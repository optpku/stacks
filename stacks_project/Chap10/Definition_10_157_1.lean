/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import ReasLib.RingTheory.Depth.Equiv
import StacksCheckRecall

/-!
@stack 031P
-/

@[expose] public section

/- Definition 10.157.1: Serre's conditions (R_k) and (S_k) for rings and modules.

Owner: `Module.SerreConditionS`, `SerreConditionR`, `SerreConditionS` in
`ReasLib.RingTheory.CohenMacaulay.SerreCondition`. -/
@[stacks 031P "(1)"]
#check @SerreConditionR
@[stacks 031P "(2)"]
#check @SerreConditionS
@[stacks 031P "(3)"]
#check @Module.SerreConditionS
#check @serreConditionR_iff
#check @serreConditionS_iff
#check @Module.serreConditionS_iff
#check @LinearEquiv.moduleDepth_eq
#check @LinearEquiv.serreConditionS_iff
#check @SerreConditionR.of_le
#check @SerreConditionS.of_le
#check @Module.SerreConditionS.of_le
