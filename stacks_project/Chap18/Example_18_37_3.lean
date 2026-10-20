module

public import ReasLib.Algebra.Module.TwistedFunction
import StacksCheckRecall

@[expose] public section

/- Example 18.37.3 (1): maps out of the acting monoid carry the coordinate-twisted module
structure. -/
@[stacks 05V9 "(1)"]
#check @TwistedFunction

/- Example 18.37.3 (2): `I(M)` is the augmentation submodule of maps vanishing at the identity. -/
@[stacks 05V9 "(2)"]
#check @TwistedFunction.augmentation

/- Example 18.37.3 (3): membership in `I(M)` is evaluation-at-one vanishing. -/
@[stacks 05V9 "(3)"]
#check @TwistedFunction.mem_augmentation_iff
