/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.CentralSimple.Splitting.Basic
import StacksCheckRecall

@[expose] public section

@[stacks 074Y] #check @CSA.IsSplitBy
#check @CSA.isSplitBy_iff_exists_pnat

end
