/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ClassGroup
import StacksCheckRecall

/-!
# Definition 31.26.7

The subgroup of principal Weil divisors and the Weil divisor class group.

@stack 0BE4
-/

@[expose] public section

open AlgebraicGeometry

universe u

section

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]

/- Definition 31.26.7: the Weil divisor class group of `X` is the quotient of the group of
Weil divisors by its subgroup of principal Weil divisors. -/
@[stacks 0BE4] #check (AlgebraicGeometry.WeilDivisorClassGroup X : Type (u + 1))

end
