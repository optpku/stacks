/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Groupoids
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Closure
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- The universe-polymorphic underlying criterion is the operational owner. -/
#check @StackOver.Groupoids.inertia.basedForget.isEquivalence_iff

/- Lemma 8.7.2: the bundled absolute inertia map is an equivalence exactly for stacks in
setoids. -/
@[stacks 04ZM]
#check @StackOver.Groupoids.inertia.forget.isEquivalence_iff
#check @BasedCategory.Inertia.cartesianForget
#check @BasedCategory.Inertia.cartesianForget.toBasedFunctor
#check @BasedCategory.Inertia.cartesianForget.toFunctor
#check @BasedCategory.Inertia.cartesianForget.obj
#check @BasedCategory.Inertia.cartesianForget.map
#check @BasedCategory.Inertia.cartesianForget.isEquivalence_iff_inSetoids
#check @StackOver.Groupoids.inertia
#check @StackOver.Groupoids.inertia.forget

end CategoryTheory
