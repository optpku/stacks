/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.TopologyComparison.Situation
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.30.2

The induced coefficient property and its pullback stability are shared topology-comparison API.
This chapter entry only recalls the reusable owners.
-/

/- Lemma 21.30.2 (0EZ9): `A_X` is the inverse image of `A'_X` under the comparison
pushforward. -/
@[stacks 0EZ9 "comparison coefficient property"] #check
  @CategoryTheory.GrothendieckTopology.TopologyComparison.objectProperty

@[stacks 0EZ9 "comparison coefficient property membership"] #check
  @CategoryTheory.GrothendieckTopology.TopologyComparison.objectProperty_mem_iff

/- Lemma 21.30.2 (0EZ9): pullback preserves the induced coefficient property. -/
@[stacks 0EZ9 "comparison coefficient property is stable under pullback"] #check
  @CategoryTheory.GrothendieckTopology.TopologyComparison.objectProperty_le_pullback
