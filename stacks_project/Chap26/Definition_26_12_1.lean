/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Properties
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry

/- Definition 26.12.1: reduced schemes use Mathlib's canonical `IsReduced` property. -/
@[stacks 01J0] #check IsReduced
#check isReduced_stalk_of_isReduced
#check isReduced_of_isReduced_stalk

end AlgebraicGeometry
