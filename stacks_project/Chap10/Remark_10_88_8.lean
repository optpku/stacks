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
