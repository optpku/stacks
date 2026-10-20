/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Over
import StacksCheckRecall

@[expose] public section

/-!
# Definition 8.4.5 — Bridge

Definition 8.4.5 defines the 2-category of stacks over a site. The canonical owner is now
`CategoryTheory.StackOver` in `CategoryTheory/Fibered/Stack/Over.lean`.
-/

namespace CategoryTheory

@[stacks 02ZG]
#check @StackOver

-- Object API
#check @StackOver.toFiberedCategoryOver
#check @StackOver.ofProjection
#check @StackOver.forget

-- Morphism API
#check @StackOver.Hom.toMor
#check @StackOver.Hom.toBasedFunctor
#check @StackOver.Hom.fiberFunctor
#check @StackOver.Hom.lift

-- 2-morphism API
#check @StackOver.Hom.toMor₂
#check @StackOver.Hom₂.toBasedNatTrans
#check @StackOver.Hom₂.toNatTrans
#check @StackOver.Hom₂.ofBasedNatTrans

end CategoryTheory
