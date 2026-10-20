/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.Oka.Disjoint
import StacksCheckRecall

/-!
# Example 10.28.3

@stack 05KA
-/

@[expose] public section

@[stacks 05KA "ideals meeting a submonoid form an Oka family"]
#check @Ideal.isOka_not_disjoint
