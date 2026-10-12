/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Stratification.Refinement
import StacksCheckRecall

@[expose] public section

/- Lemma 5.28.8: finite partitions of Noetherian spaces admit finite good locally closed
refinements. -/
@[stacks 09Y5]
#check Setoid.Partitions.exists_finite_good_refinement
