/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.IdempotentComplete
import StacksCheckRecall

@[expose] public section

/- Lemma 13.4.14 is owned by the reusable idempotent-completeness API. -/
@[stacks 05QW] #check @CategoryTheory.Pretriangulated.isIdempotentComplete_of_countableProducts
@[stacks 05QW] #check @CategoryTheory.Pretriangulated.isIdempotentComplete_of_countableCoproducts

end
