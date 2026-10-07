module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Pullback.Pseudofunctor.Action.Objects
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.12.3 (tag 04WD): pullback along a continuous functor of sites carries stacks in
groupoids to stacks in groupoids.  The primary owner retains the coverwise pullback data. -/
@[stacks 04WD]
#check @Limits.CategoricalPullback.Left.Precoverage.isStackInGroupoids

#check @StackOver.Groupoids.pullbackOfPrecoverage
#check @StackOver.Groupoids.pullbackOfPrecoverage.toGroupoids
#check @StackOver.Groupoids.pullbackOfPrecoverage.toStackOver
#check @StackOver.Groupoids.pullbackOfPrecoverage.total
#check @StackOver.Groupoids.pullbackOfPrecoverage.p
#check @StackOver.Groupoids.pullback
#check @StackOver.Groupoids.pullback_toGroupoids
#check @Limits.CategoricalPullback.Left.isStackInGroupoids

end CategoryTheory
