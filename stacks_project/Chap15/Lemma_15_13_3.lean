/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Smooth.Henselian
import StacksCheckRecall

/-!
# Smooth maps into henselian quotients

The smooth lifting theorem is already owned by `ReasLib`; this file is the labeled chapter
recall.

@stack 0H74
-/

@[expose] public section

/- Lemma 15.13.3: every map from a smooth algebra into the quotient of a henselian pair lifts
to the original ring. -/
@[stacks 0H74]
#check @Algebra.Smooth.exists_lift_of_henselian
