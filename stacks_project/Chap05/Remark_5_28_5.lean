/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Stratification.Initial
import StacksCheckRecall

@[expose] public section

/- Remark 5.28.5 (1): locally finite strata determine a closed initial family. -/
@[stacks 09Y2 "initial closed family from locally finite strata"]
#check IsStratification.initial_isClosedInitialFamily

/- Remark 5.28.5 (2): locally finite closed initial families determine frontier
stratifications. -/
@[stacks 09Y2 "locally finite frontier stratification from closed initial subsets"]
#check IsClosedInitialFamily.frontier_isStratification
