/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Principal

/-!
# Principal Weil divisors on algebraic spaces

The principal Weil divisor of a rational unit on a locally Noetherian integral
algebraic space is the locally finite sum of orders of vanishing along prime
divisors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
variable [IsLocallyNoetherian X] [IsIntegral X]

#check (AlgebraicGeometry.AlgebraicSpace.principalWeilDivisor X :
  (RationalFunction X)ˣ → WeilDivisor X)

#check (AlgebraicGeometry.AlgebraicSpace.principalWeilDivisor_coeff X :
  ∀ (f : (RationalFunction X)ˣ) (Z : PrimeDivisor X),
    (principalWeilDivisor X f).coeff Z = Z.ord f)

#check (AlgebraicGeometry.AlgebraicSpace.principalWeilDivisor_one X :
  principalWeilDivisor X 1 = 0)
