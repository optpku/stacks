/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Module.Local
import StacksCheckRecall

/-!
# Lemma 10.103.11

@stack 0AAG
-/

@[expose] public section

/- Lemma 10.103.11: localizing a Cohen--Macaulay module at any prime gives
either another Cohen--Macaulay module or the zero module. -/
@[stacks 0AAG "including the zero localization"]
#check @Module.CohenMacaulay.localizedModule_atPrime_or_subsingleton

@[stacks 0AAG "nonzero support branch"]
#check @Module.CohenMacaulay.localizedModule_atPrime
