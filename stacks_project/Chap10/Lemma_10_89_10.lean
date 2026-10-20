/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.MittagLeffler.DirectSum
import StacksCheckRecall

/-!
# Lemma 10.89.10

@stack 059P
-/

@[expose] public section

/- Chap10 Lemma 10 89 10: an arbitrary direct sum is Mittag-Leffler exactly when each summand
is Mittag-Leffler. -/
@[stacks 059P]
#check @Module.MittagLeffler.directSum_iff

@[stacks 059P "dfinsupp criterion"]
#check @Module.MittagLeffler.dfinsupp_iff

@[stacks 059P "direct-sum construction"]
#check @Module.MittagLeffler.directSum

@[stacks 059P "dfinsupp construction"]
#check @Module.MittagLeffler.dfinsupp
