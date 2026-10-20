/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Weil
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.LocallyFinite

/-!
# Principal Weil divisors on algebraic spaces

The principal Weil divisor of a rational unit on a locally Noetherian integral
algebraic space is the locally finite sum of orders of vanishing along prime
divisors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
variable [IsLocallyNoetherian X] [IsIntegral X]

/-- The principal Weil divisor associated to a unit of the ring of rational
functions. -/
def principalWeilDivisor (f : (RationalFunction X)ˣ) : WeilDivisor X :=
  WeilDivisor.ofCoeff X (fun Z ↦ Z.ord f)
    (locallyFinite_primeDivisors_ord_ne_zero X f)

/-- The coefficient of a principal Weil divisor at a prime divisor is the
corresponding order of vanishing. -/
theorem principalWeilDivisor_coeff (f : (RationalFunction X)ˣ)
    (Z : PrimeDivisor X) :
    (principalWeilDivisor X f).coeff Z = Z.ord f :=
  rfl

/-- The principal Weil divisor of the unit `1` is zero. -/
theorem principalWeilDivisor_one : principalWeilDivisor X 1 = 0 :=
  sorry

/-- The principal Weil divisor of a product of rational units is the sum of
their principal Weil divisors. -/
theorem principalWeilDivisor_mul (f g : (RationalFunction X)ˣ) :
    principalWeilDivisor X (f * g) =
      principalWeilDivisor X f + principalWeilDivisor X g :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
