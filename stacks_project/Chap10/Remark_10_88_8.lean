/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Flatness.MittagLeffler.Dual

@[expose] public section

/-!
Chapter 10, Remark 10.88.8 is the module-level form of the reusable dual criterion for a
directed system of finite free modules.

@stack 059G
-/

@[stacks 059G]
#check @Module.MittagLeffler.of_dualPresentation

#check @Module.MittagLeffler.Presentation.ofDual
#check @Module.IsMittagLefflerDirectedSystem.iff_dual
#check @Module.MittagLeffler.of_dualColimit
