/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.GroupTheory.Perm.DeletedIndex
import StacksCheckRecall

/-! @stack 01FH -/

@[expose] public section

/-
Definition 20.23.1 (01FH): the alternating Čech differential reindexes a tuple after deleting
one index.  The reusable owner is `Equiv.Perm.deleteAt`, together with its `succAbove` and sign
compatibility laws.
-/
@[stacks 01FH "deleted-index permutation for the alternating Cech differential"]
#check @Equiv.Perm.deleteAt

#check @Equiv.Perm.deleteAt_comp_succAbove
#check @Equiv.Perm.deleteAt_sign

end
