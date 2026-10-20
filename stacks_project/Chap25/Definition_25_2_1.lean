/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct
import StacksCheckRecall

/-!
# Semi-representable families

The reusable formal-coproduct and semi-representable-family API is owned by
`ReasLib.CategoryTheory.Sites.Family.FormalCoproduct`.
-/

/- Definition 25.2.1: a semi-representable object is a formal coproduct of representables. -/
@[stacks 01G0] #check @CategoryTheory.Limits.FormalCoproduct

/- The fixed-target incarnation packages each summand as an object over the target. -/
@[stacks 01G0 "fixed-target semi-representable family"]
#check @CategoryTheory.SemiRepresentableFamily.OverFamily
