/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.CentralSimple.BrauerGroup.Trivial
import StacksCheckRecall

@[expose] public section

@[stacks 074M] #check @CSA.brauerEquivalent_one
@[stacks 074M] #check @BrauerGroup.subsingleton

end
