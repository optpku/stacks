/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
