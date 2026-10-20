/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Prime
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Weil
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
@[stacks 0ENJ] #check (AlgebraicGeometry.AlgebraicSpace.PrimeDivisor X : Type (u + 1))

/- Definition 72.6.2 (2): a Weil divisor is a locally finite integer formal sum
of prime divisors. -/
@[stacks 0ENJ] #check (AlgebraicGeometry.AlgebraicSpace.WeilDivisor X : Type (u + 1))

/- Definition 72.6.2 (3): the Weil divisors on `X` form the additive commutative
group `Div(X)`. -/
@[stacks 0ENJ] #check (AlgebraicGeometry.AlgebraicSpace.instAddCommGroupWeilDivisor X :
  AddCommGroup (AlgebraicGeometry.AlgebraicSpace.WeilDivisor X))
