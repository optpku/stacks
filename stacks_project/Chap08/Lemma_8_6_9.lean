module

public import ReasLib.CategoryTheory.Fibered.Stack.PseudoPullback.Faithful
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.6.9: in a bilimit pseudopullback of stacks in groupoids, local essential
surjectivity of the left cospan leg and faithfulness of the left projection imply faithfulness
of the right cospan leg. -/
@[stacks 06DV]
#check @StackOver.Groupoids.PseudoPullback.rightFaithful
#check @StackOver.Groupoids.PseudoPullback.rightFaithful_of_faithful

#check @StackOver.Groupoids.PseudoPullback.leftFaithful
#check @StackOver.Groupoids.PseudoPullback.leftFaithful_of_faithful

end CategoryTheory
