/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Subtopos.Closed
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.43.5

The implication from a closed-subtopos presentation to a subtopos is owned by
the ReasLib closed-subtopos leaf.
-/

@[expose] public section

/- Lemma 7.43.5 (08LY): the product-projection condition defining a closed
subtopos determines a subtopos. -/
@[stacks 08LY] #check @CategoryTheory.GrothendieckTopology.IsClosedSubtopos.isSubtopos
