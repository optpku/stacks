/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.OrderOfVanishing
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Weil
public import ReasLib.AlgebraicGeometry.Scheme.FunctionField.Stalk
import ReasLib.AlgebraicGeometry.Noetherian.IrreducibleComponents
import Mathlib.Tactic.CrossRefAttribute

/-!
# Principal Weil divisors

The principal Weil divisor of a function-field unit has, at each prime divisor, the corresponding
order of vanishing as its coefficient.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

section

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]

/-- The generic-point stalks along prime divisors are discrete valuation rings. -/
class PrimeDivisorDiscreteValuationRings : Prop where
  /-- The stalk at the generic point of each prime divisor is a discrete valuation ring. -/
  isDiscreteValuationRing (Z : PrimeDivisor X) :
    IsDiscreteValuationRing (X.presheaf.stalk Z.genericPoint)

/-- Pointwise discrete-valuation-ring instances at prime-divisor generic points assemble into the
corresponding scheme-wide interface. -/
instance instPrimeDivisorDiscreteValuationRings
    [∀ Z : PrimeDivisor X, IsDiscreteValuationRing Z.genericPointStalk] :
    PrimeDivisorDiscreteValuationRings X where
  isDiscreteValuationRing Z :=
    inferInstanceAs (IsDiscreteValuationRing Z.genericPointStalk)

/-- The discrete-valuation-ring structure on the generic-point stalk of a prime divisor. -/
abbrev primeDivisorDiscreteValuationRing [h : PrimeDivisorDiscreteValuationRings X]
    (Z : PrimeDivisor X) :
    IsDiscreteValuationRing Z.genericPointStalk :=
  h.isDiscreteValuationRing Z

/-- The coefficient of the principal Weil divisor associated to a function-field unit, expressed
using discrete valuation rings at prime-divisor generic points. -/
@[stacks 0BE3]
def principalWeilDivisorCoeff
    (hDVR : ∀ Z : PrimeDivisor X, IsDiscreteValuationRing Z.genericPointStalk)
    (f : X.functionFieldˣ) (Z : PrimeDivisor X) : ℤ :=
  X.primeDivisorOrder Z f

/-- The coefficient of a principal Weil divisor is its prime-divisor order. -/
theorem principalWeilDivisorCoeff_def
    (hDVR : ∀ Z : PrimeDivisor X, IsDiscreteValuationRing Z.genericPointStalk)
    (f : X.functionFieldˣ) (Z : PrimeDivisor X) :
    principalWeilDivisorCoeff X hDVR f Z =
      X.primeDivisorOrder Z f :=
  rfl

/-- The DVR-based principal-divisor coefficient agrees with the order of vanishing on a locally
Noetherian integral scheme. -/
@[simp]
theorem principalWeilDivisorCoeff_eq_ord
    (hDVR : ∀ Z : PrimeDivisor X, IsDiscreteValuationRing Z.genericPointStalk)
    (f : X.functionFieldˣ) (Z : PrimeDivisor X) :
    principalWeilDivisorCoeff X hDVR f Z =
      X.ord (f : X.functionField) Z.genericPoint := sorry

/-- The supports of the prime divisors where a function-field unit does not belong to the image of
the generic-point stalk form a locally finite family. -/
theorem locallyFinite_primeDivisors_not_mem_genericPointStalk (f : X.functionFieldˣ) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      {x | (f : X.functionField) ∉ X.stalkInFunctionField Z.genericPoint ∧
        x ∈ (Z.support : Set X)} := sorry

/-- The supports of the prime divisors on which a nonzero rational function has nonzero order are
locally finite. -/
theorem locallyFinite_primeDivisors_ord_ne_zero (f : X.functionFieldˣ) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if X.ord (f : X.functionField) Z.genericPoint = 0 then
        (∅ : Set X)
      else
        (Z.support : Set X) := sorry

/-- The nonzero discrete-valuation coefficients of a principal Weil divisor are locally finite. -/
theorem locallyFinite_principalWeilDivisorCoeff_ne_zero
    (hDVR :
      ∀ Z : PrimeDivisor X,
        IsDiscreteValuationRing (X.presheaf.stalk Z.genericPoint))
    (f : X.functionFieldˣ) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if principalWeilDivisorCoeff X hDVR f Z = 0 then
        (∅ : Set X)
      else
        (Z.support : Set X) := sorry

/-- The principal Weil divisor associated to a function-field unit. -/
noncomputable def principalWeilDivisor (f : X.functionFieldˣ) : Div(X) :=
  WeilDivisor.ofCoeff X
    (fun Z ↦ X.ord (f : X.functionField) Z.genericPoint)
    (locallyFinite_primeDivisors_ord_ne_zero X f)

/-- The coefficient of the principal Weil divisor at a prime divisor is its order of vanishing. -/
@[simp] theorem principalWeilDivisor_coeff
    (f : X.functionFieldˣ) (Z : PrimeDivisor X) :
    (principalWeilDivisor X f).coeff Z =
      X.ord (f : X.functionField) Z.genericPoint :=
  rfl

/-- The principal Weil divisor of the unit function is zero. -/
@[simp]
theorem principalWeilDivisor_one : principalWeilDivisor X 1 = 0 := sorry

/-- The principal Weil divisor of a product is the sum of the principal Weil divisors. -/
@[simp]
theorem principalWeilDivisor_mul (f g : X.functionFieldˣ) :
    principalWeilDivisor X (f * g) =
      principalWeilDivisor X f + principalWeilDivisor X g := sorry

/-- The principal Weil divisor of an inverse is the negation of the principal Weil divisor. -/
@[simp]
theorem principalWeilDivisor_inv (f : X.functionFieldˣ) :
    principalWeilDivisor X f⁻¹ = -principalWeilDivisor X f := sorry

end

section

/-- A unit in the local ring of a prime divisor has vanishing principal coefficient. -/
theorem principalWeilDivisor_coeff_eq_zero_of_isUnit_stalk {X : Scheme.{u}}
    [IsNoetherian X] [IsIntegral X] (f : X.functionFieldˣ) (Z : PrimeDivisor X)
    (a : X.presheaf.stalk Z.genericPoint) (ha : IsUnit a)
    (hfa : algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField a = f) :
    (principalWeilDivisor X f).coeff Z = 0 := sorry

/-- If a rational function lies in the local ring of a prime divisor, its coefficient is the
length of that local ring modulo the corresponding principal ideal. -/
theorem principalWeilDivisor_coeff_eq_length {X : Scheme.{u}}
    [IsNoetherian X] [IsIntegral X] (f : X.functionFieldˣ) (Z : PrimeDivisor X)
    (a : X.presheaf.stalk Z.genericPoint)
    (hfa : algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField a = f) :
    (principalWeilDivisor X f).coeff Z =
      ((Ring.ord (X.presheaf.stalk Z.genericPoint) a).toNat : ℤ) := sorry

/-- If a rational function is a ratio `a / b` in the local ring of a prime divisor, its
coefficient is the difference of the corresponding lengths. -/
theorem principalWeilDivisor_coeff_eq_length_sub {X : Scheme.{u}}
    [IsNoetherian X] [IsIntegral X] (f : X.functionFieldˣ) (Z : PrimeDivisor X)
    (a b : X.presheaf.stalk Z.genericPoint)
    (hb : algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField b ≠ 0)
    (hfa :
      algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField a /
          algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField b =
        f) :
    (principalWeilDivisor X f).coeff Z =
      ((Ring.ord (X.presheaf.stalk Z.genericPoint) a).toNat : ℤ) -
        ((Ring.ord (X.presheaf.stalk Z.genericPoint) b).toNat : ℤ) := sorry

end

end AlgebraicGeometry.Scheme
