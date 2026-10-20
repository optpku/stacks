module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Principal
import StacksCheckRecall

/-!
# Definition 31.26.5

The principal Weil divisor associated to a function-field unit.

@stack 0BE3
-/

@[expose] public section

open AlgebraicGeometry

universe u

section

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]

/- Definition 31.26.5: the principal Weil divisor of a function-field unit has coefficient at each
prime divisor equal to its order of vanishing. -/
@[stacks 0BE3] #check (AlgebraicGeometry.Scheme.principalWeilDivisor X :
  X.functionFieldˣ → AlgebraicGeometry.WeilDivisor X)

end
