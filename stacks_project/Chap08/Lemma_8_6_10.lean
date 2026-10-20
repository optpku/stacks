module

public import ReasLib.CategoryTheory.Fibered.Stack.PseudoPullback.Equivalence
import StacksCheckRecall

@[expose] public section

/-!
# Equivalences and stack closure in a bilimit pseudopullback

The projection-equivalence criteria and the stack-in-setoids closure are owned by
`StackOver.Groupoids.PseudoPullback`. This chapter file retains the source label only.
-/

namespace CategoryTheory

/- A global equivalence on one cospan leg makes the opposite projection an equivalence. -/
#check @Bicategory.PseudoPullbackCone.sndEquivalence
#check @Bicategory.PseudoPullbackCone.fstEquivalence
#check @StackOver.Groupoids.PseudoPullback.sndIsEquivalence
#check @StackOver.Groupoids.PseudoPullback.fstIsEquivalence
#check @StackOver.Groupoids.PseudoPullback.IsEquivalence.rightInSetoids
#check @StackOver.Groupoids.PseudoPullback.IsEquivalence.leftInSetoids

/- Lemma 8.6.10: a fully faithful, locally essentially surjective cospan leg transports the
stack-in-setoids condition across a bilimit pseudopullback. -/
@[stacks 05W9]
#check @StackOver.Groupoids.PseudoPullback.rightInSetoids.ofFullyFaithful

#check @StackOver.Groupoids.PseudoPullback.leftInSetoids.ofFullyFaithful

end CategoryTheory
