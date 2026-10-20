/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.MittagLeffler.TensorProduct
import StacksCheckRecall

/-!
# Restriction of scalars for Mittag-Leffler modules

@stack 05CT
-/

@[expose] public section

/- Lemma 10.89.11: restriction of scalars preserves Mittag-Leffler modules
under the source flatness and Mittag-Leffler hypotheses. -/
@[stacks 05CT]
#check @Module.MittagLeffler.RestrictScalars.of_flat
