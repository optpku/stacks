/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Ring
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.104.6

@stack 00NC
-/

/- Definition 10.104.6: a Cohen--Macaulay ring is Noetherian and is
Cohen--Macaulay after localization at every prime. -/
@[stacks 00NC]
#check @CohenMacaulayRing
