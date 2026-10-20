/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Stackification
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.8.5 (06NS): inertia commutes with stackification. Preservation of local equivalences
is the reusable input, while the fibered-category statements are fixed-universe companions. -/
@[stacks 06NS "inertia preserves stackifications"]
#check @CartesianBasedFunctor.Inertia.map.isStackification

#check @CartesianBasedFunctor.Inertia.map
#check @CartesianBasedFunctor.Inertia.map.isLocalEquivalence
#check @FiberedCategoryOver.Inertia.map.isLocalEquivalence
#check @FiberedCategoryOver.Inertia.map.isStackification

end CategoryTheory
