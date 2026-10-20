/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.HenselianFraction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Prime
public import Mathlib.RingTheory.OrderOfVanishing.Basic

/-! # Orders of rational units along prime divisors -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable [hN : IsLocallyNoetherian X] [hI : IsIntegral X]

namespace PrimeDivisor

/-- The canonical function-field comparison at the generic point of a prime divisor. -/
def functionFieldToHenselianFraction (Z : PrimeDivisor X) :
    RationalFunction X →+* FractionRing (henselianLocalRing X Z.genericPoint) :=
  rationalFunctionToHenselianFraction Z.genericPoint

/-- Membership of a rational function in the image of `O_{X, ξ}^h` inside
its total quotient ring. -/
def mem_henselianLocalRing (Z : PrimeDivisor X) (f : RationalFunction X) : Prop :=
  functionFieldToHenselianFraction Z f ∈
    Set.range
      (algebraMap (henselianLocalRing X Z.genericPoint)
        (FractionRing (henselianLocalRing X Z.genericPoint)))

/-- Henselian local-ring membership is the existence of a preimage under the
canonical total-quotient algebra map. -/
theorem mem_henselianLocalRing_iff (Z : PrimeDivisor X) (f : RationalFunction X) :
    mem_henselianLocalRing Z f ↔
      ∃ a : henselianLocalRing X Z.genericPoint,
        algebraMap (henselianLocalRing X Z.genericPoint)
            (FractionRing (henselianLocalRing X Z.genericPoint)) a =
          functionFieldToHenselianFraction Z f :=
  Iff.rfl

/-- The order of vanishing of a rational unit along a prime divisor, as the
length difference of a nonzerodivisor representation of its image under
`functionFieldToHenselianFraction`. -/
def ord (Z : PrimeDivisor X) (f : (RationalFunction X)ˣ) : ℤ :=
  let A := henselianLocalRing X Z.genericPoint
  let ab :=
    IsLocalization.sec (nonZeroDivisors A)
      (functionFieldToHenselianFraction Z (f : RationalFunction X))
  ((Ring.ord A ab.1).toNat : ℤ) - ((Ring.ord A (ab.2 : A)).toNat : ℤ)

include hN hI in
/-- A nonzerodivisor in the henselian local ring at a prime-divisor generic point
has a principal quotient of finite length. -/
theorem ord_finite_of_mem_nonZeroDivisors (Z : PrimeDivisor X)
    (a : henselianLocalRing X Z.genericPoint)
    (ha : a ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint)) :
    Ring.ord (henselianLocalRing X Z.genericPoint) a ≠ ⊤ :=
  sorry

/-- If `functionFieldToHenselianFraction` sends `f` to `IsLocalization.mk' a ⟨b, hb⟩`
with `a` and `b` nonzerodivisors, then the order is the corresponding length
difference in `O_{X, ξ}^h`. -/
theorem ord_spec (Z : PrimeDivisor X) (f : (RationalFunction X)ˣ)
    (a b : henselianLocalRing X Z.genericPoint)
    (ha : a ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hb : b ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hrep :
      functionFieldToHenselianFraction Z (f : RationalFunction X) =
        IsLocalization.mk'
          (FractionRing (henselianLocalRing X Z.genericPoint)) a ⟨b, hb⟩) :
    ord Z f =
      ((Ring.ord (henselianLocalRing X Z.genericPoint) a).toNat : ℤ) -
        ((Ring.ord (henselianLocalRing X Z.genericPoint) b).toNat : ℤ) :=
  sorry

/-- The order is the difference of principal-quotient lengths in `O_{X, ξ}^h`. -/
theorem ord_eq_length (Z : PrimeDivisor X) (f : (RationalFunction X)ˣ)
    (a b : henselianLocalRing X Z.genericPoint)
    (ha : a ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hb : b ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hrep : functionFieldToHenselianFraction Z (f : RationalFunction X) =
      IsLocalization.mk' (FractionRing (henselianLocalRing X Z.genericPoint))
        a ⟨b, hb⟩) :
    ord Z f =
      ((Module.length (henselianLocalRing X Z.genericPoint)
          (henselianLocalRing X Z.genericPoint ⧸ Ideal.span {a})).toNat : ℤ) -
        ((Module.length (henselianLocalRing X Z.genericPoint)
          (henselianLocalRing X Z.genericPoint ⧸ Ideal.span {b})).toNat : ℤ) := by
  exact ord_spec Z f a b ha hb hrep

/-- The order of vanishing of a product of rational units along a prime divisor is
the sum of their orders of vanishing. -/
theorem ord_mul (Z : PrimeDivisor X) (f g : (RationalFunction X)ˣ) :
    Z.ord (f * g) = Z.ord f + Z.ord g :=
  sorry

end PrimeDivisor

end AlgebraicGeometry.AlgebraicSpace
