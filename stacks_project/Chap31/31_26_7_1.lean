module

import ReasLib.AlgebraicGeometry.Scheme.Divisor.ClassGroup
import StacksCheckRecall

open AlgebraicGeometry

universe u

section

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]

/- 31.26.7.1: The sequence from function-field units through Weil divisors to the Weil divisor
class group is right-exact. -/
@[stacks 0BE5] #check
  (AlgebraicGeometry.weilDivisorClass_exactSequence X :
    Function.Exact (AlgebraicGeometry.Scheme.principalWeilDivisor X)
        (AlgebraicGeometry.weilDivisorClassGroupMk X) ∧
      Function.Surjective (AlgebraicGeometry.weilDivisorClassGroupMk X))

end
