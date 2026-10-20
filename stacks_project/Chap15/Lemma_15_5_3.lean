/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Pullback.LocalizationAway

/-!
# Lemma 15.5.3

@stack 01Z8

The reusable localized-pullback theorem and its canonical right comparison map are owned by
`CategoryTheory.IsPullback.localizationAway` and
`CategoryTheory.IsPullback.localizationAwayRightMap`.
-/

@[expose] public section

/- @stack 01Z8 -/
@[stacks 01Z8 "Lemma 15.5.3"]
#check @CategoryTheory.IsPullback.localizationAway

#check @CategoryTheory.IsPullback.localizationAwayRightMap
#check @CategoryTheory.IsPullback.localizationAwayRightMap_algebraMap_apply
