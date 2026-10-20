/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.FullSubcategory.Small
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Remark 8.4.9: a stack with essentially small fibers has a small, essentially surjective full
subcategory model that remains a stack. -/
@[stacks 03ZZ]
#check @StackOver.SmallModel.nonemptyOfEssentiallySmall
#check @StackOver.SmallModel.nonemptyOfProjection
#check @StackOver.SmallModel.source
#check @StackOver.SmallModel.source.p
#check @StackOver.SmallModel.source.total
#check @StackOver.SmallModel.sourceSmall
#check @StackOver.SmallModel.inclusion
#check @StackOver.SmallModel.inclusion.toBasedFunctor
#check @StackOver.SmallModel.inclusion.toFunctor
#check @StackOver.SmallModel.inclusion.isEquivalence

/- The textbook language of representatives of isomorphism classes is the explicit form of
fiberwise essential smallness. -/
#check @ObjectProperty.EssentiallySmall.exists_set_representatives

end CategoryTheory
