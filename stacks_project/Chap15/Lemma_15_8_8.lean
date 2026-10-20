/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.FittingIdeal.LocallyFree
import StacksCheckRecall

/-!
# Fitting ideals and finite locally free modules

@stack 07ZD
-/

-- Lemma 15.8.8: finite local freeness of rank `r` is equivalent to the prescribed pattern of
-- vanishing and unit Fitting ideals.
@[stacks 07ZD "finite locally free modules detected by Fitting ideals"]
#check @FittingIdeal.finiteLocallyFreeOfRank_tfae
