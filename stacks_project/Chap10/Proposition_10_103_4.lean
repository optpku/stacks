/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Module.RegularSequence
import StacksCheckRecall

/-!
# Expected-codimension sequences on Cohen--Macaulay modules

@stack 00N6
-/

@[expose] public section

@[stacks 00N6 "(1)"]
#check @Module.CohenMacaulay.isRegular_of_supportDim_quotient_add_length_eq

@[stacks 00N6 "(2)"]
#check @Module.CohenMacaulay.exists_maximal_regular_extension_of_supportDim_quotient_add_length_eq_of_nat
