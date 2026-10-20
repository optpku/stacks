/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.LowerShriek
import StacksCheckRecall

@[expose] public section

open CategoryTheory

namespace CategoryTheory.FiberedCategoryOver

/- Shared support for Lemma 21.38.5 (08PC): inverse image and lower shriek for a morphism of
fibered categories are owned by `ReasLib.CategoryTheory.Fibered.LowerShriek`. -/
@[stacks 08PC "inherited topology"]
#check @sourceTopology

@[stacks 08PC "module inverse image"]
#check @moduleInverseImage

@[stacks 08PC "abelian inverse image"]
#check @abelianInverseImage

@[stacks 08PC "module lower shriek"]
#check @moduleLowerShriek

@[stacks 08PC "abelian lower shriek"]
#check @abelianLowerShriek

@[stacks 08PC "module and abelian lower shriek comparison"]
#check @lowerShriekForgetComparison

end CategoryTheory.FiberedCategoryOver
