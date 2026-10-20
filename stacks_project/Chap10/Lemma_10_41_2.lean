/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.GoingDown
import StacksCheckRecall

/-!
# Open spectrum maps satisfy going down

@stack 0407
-/

@[expose] public section

/- Lemma 10.41.2: an open map on prime spectra implies going down. -/
@[stacks 0407]
#check @Algebra.HasGoingDown.of_isOpenMap
