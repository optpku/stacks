/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Weil
import Mathlib.AlgebraicGeometry.Noetherian
import StacksCheckRecall

/-!
# Definition 31.26.2

Prime divisors and locally finite Weil divisors on a scheme.
-/

@[expose] public section

universe u

section

variable (X : AlgebraicGeometry.Scheme.{u})
variable [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsIntegral X]

/- Definition 31.26.2 (1): a prime divisor is an integral closed subscheme of codimension one. -/
@[stacks 0BE2] #check
  (AlgebraicGeometry.PrimeDivisor X : Type u)

/- Definition 31.26.2 (2): a Weil divisor is a locally finite integer formal sum of prime
divisors. -/
@[stacks 0BE2] #check
  (AlgebraicGeometry.WeilDivisor X : Type u)

/- Definition 31.26.2 (3): the Weil divisors on `X` form the additive commutative group
`Div(X)`. -/
@[stacks 0BE2] #check
  (AlgebraicGeometry.instAddCommGroupWeilDivisor X :
    AddCommGroup (AlgebraicGeometry.WeilDivisor X))

end
