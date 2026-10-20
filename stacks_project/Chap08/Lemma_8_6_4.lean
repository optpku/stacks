module

public import ReasLib.CategoryTheory.Fibered.Stack.Equivalence
import StacksCheckRecall

@[expose] public section

/-!
# Equivalence invariance for stacks in setoids

Thinness of the fibers and the stack condition are transported together by the shared
`IsStack.InSetoids` owner theorem.
-/

namespace CategoryTheory

/- Lemma 8.6.4: stack-in-setoids conditions are invariant under an equivalence over the base. -/
@[stacks 0431]
#check @IsStack.InSetoids.iff_of_isEquivalence

end CategoryTheory
