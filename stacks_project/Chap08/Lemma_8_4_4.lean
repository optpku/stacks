/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Equivalence
import StacksCheckRecall

@[expose] public section

/-!
# Equivalence invariance of the stack condition

The reusable owner is `IsStack.OnSite.iff_of_isEquivalence`; this file records the source label and
keeps the source's explicit equivalence witness visible.
-/

namespace CategoryTheory

/- Lemma 8.4.4: stack conditions are invariant under an equivalence over the base. -/
@[stacks 042W]
#check @IsStack.OnSite.iff_of_isEquivalence

end CategoryTheory
