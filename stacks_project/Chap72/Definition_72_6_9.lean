/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.ClassGroup
import StacksCheckRecall

/-!
# Definition 72.6.9

The Weil divisor class group of a locally Noetherian integral algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
variable [IsLocallyNoetherian X] [IsIntegral X]

/- Definition 72.6.9: Let `S` be a scheme. Let `X` be a locally Noetherian integral algebraic
space over `S`. The Weil divisor class group of `X` is the quotient of the group of Weil
divisors by the subgroup of principal Weil divisors. Notation: Cl(X). -/
@[stacks 0ENR] #check (AlgebraicGeometry.AlgebraicSpace.WeilDivisorClassGroup X : Type (u + 1))
