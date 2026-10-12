/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Constructible.Subspace
import StacksCheckRecall

@[expose] public section

/- Lemma 5.15.8: constructible subsets restrict to retrocompact subspaces of
prespectral spaces. -/
@[stacks 09YF]
#check Topology.IsConstructible.preimage_subtypeVal_of_isRetrocompact
