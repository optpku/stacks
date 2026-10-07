module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap72.Definition_72_6_2_Prime
public import stacks_project.Chap72.Definition_72_6_2_Weil
import StacksCheckRecall

/-!
# Definition 72.6.2

Prime divisors and locally finite Weil divisors on a locally Noetherian
integral algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
variable [IsLocallyNoetherian X] [IsIntegral X]

/- Definition 72.6.2 (1): a prime divisor is an integral closed subspace of
codimension one. -/
@[stacks 0ENJ] #check PrimeDivisor X

/- Definition 72.6.2 (2): a Weil divisor is a locally finite integer formal sum
of prime divisors. -/
@[stacks 0ENJ] #check WeilDivisor X

/- Definition 72.6.2 (3): the Weil divisors on `X` form the additive commutative
group `Div(X)`. -/
@[stacks 0ENJ] #check instAddCommGroupWeilDivisor X
