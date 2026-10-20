/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.CentralSimple.BrauerGroup.Group
import StacksCheckRecall

@[expose] public section

section
variable {k : Type*} [Field k]

@[stacks 074L] #check (inferInstance : CommGroup (BrauerGroup k))
@[stacks 074L] #check @BrauerGroup.one_def
@[stacks 074L] #check @BrauerGroup.mk_mul_mk
@[stacks 074L] #check @BrauerGroup.mk_inv

end

end
