/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.CentralSimple.BrauerGroup.Trivial
import StacksCheckRecall

@[expose] public section

@[stacks 074M] #check @CSA.brauerEquivalent_one
@[stacks 074M] #check @BrauerGroup.subsingleton

end
