/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber.TwoCell
public import ReasLib.CategoryTheory.Fibered.LowerShriek.Derived
import StacksCheckRecall

@[expose] public section

open CategoryTheory

namespace CategoryTheory.FiberedCategoryOver

/- Remark 21.38.6 (09CY): specialize the ordinary and derived lower-shriek constructions of
Lemma 21.38.5 to the canonical projection `toBase P`. -/
@[stacks 09CY "canonical projection morphism"]
#check @toBase

@[stacks 09CY "ordinary projection lower shrieks"]
#check @moduleLowerShriek

@[stacks 09CY "ordinary projection abelian lower shriek"]
#check @abelianLowerShriek

@[stacks 09CY "ordinary projection forgetful comparison"]
#check @lowerShriekForgetComparison

@[stacks 09CY "ordinary projection forgetful comparison is invertible"]
#check @lowerShriekForgetComparison_isIso

namespace DerivedLowerShriek

@[stacks 09CY "derived projection lower shrieks"]
#check @moduleLowerShriek

@[stacks 09CY "derived projection abelian lower shriek"]
#check @abelianLowerShriek

@[stacks 09CY "derived projection forgetful comparison"]
#check @underlyingComparison

@[stacks 09CY "derived projection forgetful comparison is invertible"]
#check @underlyingComparison_isIso

end DerivedLowerShriek

end CategoryTheory.FiberedCategoryOver
