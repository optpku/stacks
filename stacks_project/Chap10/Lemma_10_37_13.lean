/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Normal.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Normality and localization

Lemma 10.37.13, tag `037C`, is owned by the reusable normal-localization API.

@stack 037C
-/

/- Lemma 10.37.13, tag `037C`: an arbitrary localization of a normal ring is
normal. -/
@[stacks 037C]
#check @IsNormalRing.of_isLocalization

/- Lemma 10.37.13, tag `037C`: the canonical localization carries the
corresponding normal-ring instance. -/
@[stacks 037C]
#check @Localization.instIsNormalRing
