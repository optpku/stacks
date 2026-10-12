/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.CentralSimple.SkolemNoether
import StacksCheckRecall

@[expose] public section

@[stacks 074R] #check @CSA.algEquiv_isInner
#check @CSA.autInner
#check @CSA.autInner_apply

end
