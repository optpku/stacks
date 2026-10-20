/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Definition 8.6.1 — Bridge

Definition 8.6.1 defines stacks in setoids and stacks in sets. The canonical owners are now
`CategoryTheory.IsStack.InSetoids` and `CategoryTheory.IsStack.InSets` in
`CategoryTheory/Fibered/Stack/InSetoids.lean`; their bundled full-subcategory owners are
`StackOver.Setoids` and `StackOver.Sets`.
-/

namespace CategoryTheory

@[stacks 042Z]
#check @IsStack.InSetoids

@[stacks 042Z "stacks in sets"]
#check @IsStack.InSets
#check @IsStack.InSetoids.iff_fibered_and_stackOnSite
#check @IsStack.InSetoids.iff_stackOnSite_and_fibersSetoid
#check @IsStack.InSetoids.toOnSite
#check @IsStack.InSets.iff_discreteFibration_and_stackOnSite
#check @IsStack.InSets.iff_stackOnSite_and_fibersDiscrete
#check @IsStack.InSets.toOnSite
#check @StackOver.Setoids
#check @StackOver.Sets
#check @StackOver.Sets.mk
#check @StackOver.Sets.mk.toSetsIso
#check @StackOver.Sets.toSets

end CategoryTheory
