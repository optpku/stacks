/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.CentralSimple.SkolemNoether
import StacksCheckRecall

@[expose] public section

@[stacks 074R] #check @CSA.algEquiv_isInner
#check @CSA.autInner
#check @CSA.autInner_apply

end
