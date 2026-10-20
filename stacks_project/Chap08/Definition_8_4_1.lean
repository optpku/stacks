/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.DescentData.Cover
public import ReasLib.CategoryTheory.Fibered.Stack.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Definition 8.4.1 -- Stack condition on a fibered category

The canonical owner is `CategoryTheory.IsStack.OnSite`.  The induced descent functors belong to
the fiber-pseudofunctor strong transformation API and the semantic
`FiberedCategoryOver.Descent` namespace.
-/

namespace CategoryTheory

/- Definition 8.4.1: a stack over `(C, J)` is a fibered category whose canonical fiber
pseudofunctor satisfies the stack condition for `J`. -/
@[stacks 026F "stack condition for a fibered category"]
#check @IsStack.OnSite
#check @IsStack.OnSite.iff_stack
#check @IsStack.OnSite.toPrestack
#check @IsPrestack.OnSite.iff_prestack
#check @IsPrestack.OnSite.sheafHom

#check @Pseudofunctor.StrongTrans.descentFunctor
#check @FiberedCategoryOver.Descent.functor
#check @FiberedCategoryOver.Descent.Cover.functor

end CategoryTheory
