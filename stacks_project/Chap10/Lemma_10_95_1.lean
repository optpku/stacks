/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Flatness.MittagLeffler.BaseChange

@[expose] public section

/-!
Chapter 10, Lemma 10.95.1 is the faithfully flat specialization of reflection along a
universally injective algebra map.

@stack 05A5
-/

@[stacks 05A5]
#check @Module.MittagLeffler.of_baseChange

@[stacks 05A5 "universally injective base change"]
#check @Module.MittagLeffler.BaseChange.of_universallyInjective

@[stacks 05A5 "base-change equivalence"]
#check @Module.MittagLeffler.iff_baseChange
