module

import ReasLib.CategoryTheory.Pretriangulated.IdempotentComplete
import StacksCheckRecall

@[expose] public section

/- Lemma 13.4.14 is owned by the reusable idempotent-completeness API. -/
@[stacks 05QW] #check @CategoryTheory.Pretriangulated.isIdempotentComplete_of_countableProducts
@[stacks 05QW] #check @CategoryTheory.Pretriangulated.isIdempotentComplete_of_countableCoproducts

end
