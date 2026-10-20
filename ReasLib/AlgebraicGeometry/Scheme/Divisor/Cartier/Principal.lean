/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FunctionField.MeromorphicFunctions
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Cartier.Weil

/-!
# Principal Cartier divisors

A nonzero rational function on an integral scheme defines a Cartier divisor through its
meromorphic unit. On a Noetherian integral scheme, its associated Weil divisor is the
principal Weil divisor of the rational function.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsIntegral X]

variable [HasSheafify (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X.toTopCat).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]

/-- The principal Cartier divisor associated to a rational function, as the image of its
meromorphic unit in `𝒦_X^⁎ / 𝒪_X^⁎`. -/
def principalCartierDivisor (f : X.functionFieldˣ) : CartierDivisor X :=
  ofMeromorphicUnits X (meromorphicUnitOfFunctionField X f)

/-- A principal Cartier divisor is the cokernel class of the associated meromorphic unit. -/
theorem principalCartierDivisor_eq_ofMeromorphicUnits (f : X.functionFieldˣ) :
    principalCartierDivisor X f =
      ofMeromorphicUnits X (meromorphicUnitOfFunctionField X f) :=
  rfl

/-- The principal Cartier divisor of the unit function is zero. -/
theorem principalCartierDivisor_one : principalCartierDivisor X 1 = 0 :=
  sorry

/-- The principal Cartier divisor of a product is the sum of the principal Cartier
divisors. -/
theorem principalCartierDivisor_mul (f g : X.functionFieldˣ) :
    principalCartierDivisor X (f * g) =
      principalCartierDivisor X f + principalCartierDivisor X g :=
  sorry

/-- The principal Cartier divisor of an inverse is the negation of the principal Cartier
divisor. -/
theorem principalCartierDivisor_inv (f : X.functionFieldˣ) :
    principalCartierDivisor X f⁻¹ = -principalCartierDivisor X f :=
  sorry

/-- The Cartier order of a principal Cartier divisor along a prime divisor is the order of
vanishing of the rational function. -/
theorem cartierOrder_principalCartierDivisor [IsNoetherian X] (f : X.functionFieldˣ)
    (Z : PrimeDivisor X) :
    cartierOrder (principalCartierDivisor X f) Z =
      X.ord (f : X.functionField) Z.genericPoint :=
  sorry

/-- On a Noetherian integral scheme, the Weil divisor associated to the principal Cartier
divisor of a nonzero rational function is its principal Weil divisor. -/
@[stacks 02F7]
theorem weilDivisor_ofCartier_principalCartierDivisor
    {X : Scheme.{u}} [IsNoetherian X] [IsIntegral X]
    [HasSheafify (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.toTopCat).HasSheafCompose
      (CategoryTheory.forget CommRingCat.{u})]
    (f : X.functionFieldˣ) :
    weilDivisor_ofCartier (principalCartierDivisor X f) = principalWeilDivisor X f :=
  sorry

end AlgebraicGeometry.Scheme
