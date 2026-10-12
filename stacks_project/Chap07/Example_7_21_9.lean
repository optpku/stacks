/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Category.TopCat.Subset.Cocontinuity

import StacksCheckRecall

@[expose] public section

/-!
[stacks 00XV]

Example 7.21.9 records the density obstruction for cocontinuous restriction to a subspace and
the punctured-real counterexample to its converse.
-/

@[stacks 00XV] #check TopologicalSpace.Opens.map_ne_bot_of_isCocontinuous
#check TopCat.Subset.dense_of_isCocontinuous
#check TopCat.Subset.inter_nonempty_of_isCocontinuous
@[stacks 00XV "punctured-real counterexample"] #check TopCat.Subset.puncturedReal_not_isCocontinuous
