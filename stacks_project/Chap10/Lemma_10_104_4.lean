/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Module.Self
import StacksCheckRecall

@[expose] public section

/-!
# Dimension formula for a Cohen-Macaulay local ring

@stack 00NA
-/

/- Lemma 10.104.4: the dimension of a Noetherian local Cohen-Macaulay ring is the sum of the
dimensions of its localization and quotient at any prime. -/
@[stacks 00NA]
#check @Module.CohenMacaulay.ringKrullDim_eq_localizationAtPrime_add_quotient_self
