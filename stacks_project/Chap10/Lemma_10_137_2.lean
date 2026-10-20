/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Localization

@[expose] public section

/-!
# Smooth Localization Recall

@stack 00T3

The intrinsic ring-hom localization theorems live in ReasLib; the algebra
forms below are the direct source-facing views.
-/

/- Lemma 10.137.2 (1), tag 00T3: localizing a smooth `R`-algebra away from an
element of its target remains smooth over `R`. -/
@[stacks 00T3 "smoothness under target localization"]
#check @Algebra.Smooth.localizationAway

/- Lemma 10.137.2 (2), tag 00T3: if an element of the base becomes a unit in
a smooth algebra, the induced away-localization map is smooth. -/
@[stacks 00T3 "smoothness under source localization"]
#check @Algebra.Smooth.awayLift
