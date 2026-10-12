/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Constructible.Subspace
import StacksCheckRecall

@[expose] public section

/- Lemma 5.15.7: constructible subsets restrict to closed subspaces with
compact complement. -/
@[stacks 09YE]
#check Topology.IsConstructible.preimage_subtypeVal_of_isClosed_of_isCompact_compl
