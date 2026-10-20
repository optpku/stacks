/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Pullback.Pseudofunctor.Action.Objects
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.12.2 (tag 04WC): pullback along a continuous functor of sites carries stacks to
stacks.  The primary owner retains precoverages and asks only for the pullbacks occurring in
covering families. -/
@[stacks 04WC]
#check @Limits.CategoricalPullback.Left.Precoverage.isStackOnSite

#check @StackOver.pullbackOfPrecoverage
#check @StackOver.pullbackOfPrecoverage.toFiberedCategoryOver
#check @StackOver.pullbackOfPrecoverage.total
#check @StackOver.pullbackOfPrecoverage.p
#check @StackOver.pullback
#check @StackOver.pullback_toFiberedCategoryOver
#check @StackOver.pullback_total
#check @StackOver.pullback_p
#check @Limits.CategoricalPullback.Left.isStackOnSite

end CategoryTheory
