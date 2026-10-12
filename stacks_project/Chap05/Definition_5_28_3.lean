/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Stratification.Indexed
import StacksCheckRecall

@[expose] public section

/- Definition 5.28.3: the ordered locally closed family is the reusable indexed
stratification predicate. -/
@[stacks 09Y1]
#check IsStratification

/- Empty indexed strata are discarded by the canonical locally closed partition view. -/
#check IsStratification.toLocallyClosedPartition
