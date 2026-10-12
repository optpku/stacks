/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Constructible.Subspace
import StacksCheckRecall

@[expose] public section

/- Lemma 5.15.12: constructible subsets of constructible subspaces have
constructible ambient image. -/
@[stacks 09YJ]
#check Topology.IsConstructible.image_subtypeVal_of_isConstructible
