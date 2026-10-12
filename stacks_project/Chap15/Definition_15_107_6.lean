/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.Branches
import StacksCheckRecall

/-!
# Definition 15.107.6

@stack 0C26
-/

@[expose] public section

/- Definition 15.107.6: the branch-number and geometric-branch-number
invariants of local rings are owned by `ReasLib.RingTheory.LocalRing.Branches`. -/
@[stacks 0C26 "(1) branch number"]
#check @branchNumber
@[stacks 0C26 "(2) geometric branch number"]
#check @geometricBranchNumber
