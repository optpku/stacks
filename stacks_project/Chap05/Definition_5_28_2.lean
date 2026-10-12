/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Stratification.Good
import StacksCheckRecall

@[expose] public section

/- Definition 5.28.2: the frontier condition is the reusable predicate on a locally closed
partition. -/
@[stacks 09Y0]
#check LocallyClosedPartition.IsGood
