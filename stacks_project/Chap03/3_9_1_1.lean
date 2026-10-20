module

public import ReasLib.SetTheory.Cardinal.Bound
import StacksCheckRecall

@[expose] public section

universe u

open scoped Cardinal

/- 3.9.1.1: The bound of a cardinal is the maximum of its countable power and its successor. -/
@[stacks 046U] #check (Cardinal.countableSuccBound_eq :
  ∀ kappa : Cardinal.{u},
    Cardinal.countableSuccBound kappa = max (kappa ^ ℵ₀) (Order.succ kappa))
