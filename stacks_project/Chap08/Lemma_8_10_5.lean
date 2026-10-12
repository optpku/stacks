/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.InheritedTopology
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.10.5 (tag 06NX): a fibred-in-groupoids morphism of stacks in groupoids is a stack
in groupoids for the topology inherited from its target.  The projection-level theorem is the
universe-polymorphic owner; the bundled statement is a downstream convenience. -/
@[stacks 06NX]
#check @IsStack.InGroupoids.of_comp_inheritedTopology

#check @StackOver.Groupoids.Hom.inheritedTopology.isStackInGroupoids

end CategoryTheory
