/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Projective.InfiniteRank
import StacksCheckRecall

/-!
# Theorem 15.129.6

@stack 0GVK

The infinite-rank freeness theorem is recalled from its canonical ReasLib owner.
-/

@[expose] public section

-- Theorem 15.129.6: countably generated projective modules of infinite local rank are free.
@[stacks 0GVK]
#check @Module.Projective.freeOfCountablyGeneratedOfInfiniteRankAtMaximal
