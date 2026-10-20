module

import ReasLib.CategoryTheory.Pretriangulated.Homological.Opposite.FiveTerm
import StacksCheckRecall

@[expose] public section

/-!
# 13.3.5.1

The centered five-term row of a contravariant cohomological functor and its
exactness are owned by `Functor.Cohomological`.
-/

/- 13.3.5.1: the centered five-term cohomology row attached to a distinguished
triangle is exact. -/
@[stacks 0148] #check @CategoryTheory.Functor.Cohomological.fiveTerm_exact

/- Companion check: the row itself is reusable concrete data. -/
@[stacks 0148] #check @CategoryTheory.Functor.Cohomological.fiveTerm
