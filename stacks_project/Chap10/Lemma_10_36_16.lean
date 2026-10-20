/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.IntegralClosure.Transitivity
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.36.16 (Tag 0308): transitivity of integral closures.

@stack 0308
-/

-- Lemma 10.36.16: if `B'` is the integral closure of `A` in `B` and `C'` is the integral
-- closure of `B'` in `C`, then `C'` is the integral closure of `A` in `C`.
@[stacks 0308]
#check @IsIntegralClosure.trans
