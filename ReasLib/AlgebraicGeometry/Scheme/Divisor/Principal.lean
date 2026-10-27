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
      X.ord (f : X.functionField) Z.genericPoint :=
  rfl

private theorem ord_eq_zero_of_isUnit_stalk (x : X) (a : X.presheaf.stalk x)
    (ha : IsUnit a) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x = 0 := by
  by_cases hx : Order.coheight x = 1
  · letI : Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
      krullDimLE_of_coheight_le hx.le
    rw [ord_eq_ordHom_of_coheight_eq_one hx]
    change Multiplicative.toAdd
      ((Ring.ordFrac (X.presheaf.stalk x)
        (algebraMap (X.presheaf.stalk x) X.functionField a)).unzeroD 1) = 0
    simp [Ring.ordFrac_of_isUnit ha]
  · exact X.ord_eq_zero_of_coheight_neq_one hx _

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
        (Z.support : Set X) := by
  intro x
  obtain ⟨s, hs, hfs⟩ := locallyFinite_primeDivisors_not_mem_genericPointStalk X f x
  obtain ⟨t, ht, hft⟩ := locallyFinite_primeDivisors_not_mem_genericPointStalk X f⁻¹ x
  refine ⟨s ∩ t, Filter.inter_mem hs ht, (hfs.union hft).subset ?_⟩
  rintro Z ⟨y, hy, hys, hyt⟩
  by_cases hord : X.ord (f : X.functionField) Z.genericPoint = 0
  · simp [hord] at hy
  · have hyZ : y ∈ (Z.support : Set X) := by
      simpa [hord] using hy
    by_cases hf : (f : X.functionField) ∈ X.stalkInFunctionField Z.genericPoint
    · right
      refine ⟨y, ⟨?_, hyZ⟩, hyt⟩
      intro hfinv
      obtain ⟨a, ha⟩ := hf
      obtain ⟨b, hb⟩ := hfinv
      have hab : a * b = 1 := by
        apply IsFractionRing.injective (X.presheaf.stalk Z.genericPoint) X.functionField
        rw [map_mul, ha, hb, map_one]
        exact f.mul_inv
      apply hord
      rw [← ha]
      exact ord_eq_zero_of_isUnit_stalk X Z.genericPoint a (IsUnit.of_mul_eq_one b hab)
    · exact Or.inl ⟨y, ⟨hf, hyZ⟩, hys⟩

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
        (Z.support : Set X) := by
  exact locallyFinite_primeDivisors_ord_ne_zero X f

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
theorem principalWeilDivisor_one : principalWeilDivisor X 1 = 0 := by
  apply WeilDivisor.ext X
  intro Z
  change X.ord (1 : X.functionField) Z.genericPoint = 0
  by_cases hZ : Order.coheight Z.genericPoint = 1
  · simp [ord_eq_ordHom_of_coheight_eq_one hZ]
  · exact X.ord_eq_zero_of_coheight_neq_one hZ 1

/-- The principal Weil divisor of a product is the sum of the principal Weil divisors. -/
@[simp]
theorem principalWeilDivisor_mul (f g : X.functionFieldˣ) :
    principalWeilDivisor X (f * g) =
      principalWeilDivisor X f + principalWeilDivisor X g := by
  apply WeilDivisor.ext X
  intro Z
  exact X.ord_mul f.ne_zero g.ne_zero

/-- The principal Weil divisor of an inverse is the negation of the principal Weil divisor. -/
@[simp]
theorem principalWeilDivisor_inv (f : X.functionFieldˣ) :
    principalWeilDivisor X f⁻¹ = -principalWeilDivisor X f := by
  apply eq_neg_iff_add_eq_zero.mpr
  rw [← principalWeilDivisor_mul, inv_mul_cancel, principalWeilDivisor_one]

end

section

private theorem primeDivisor_genericPoint_coheight {X : Scheme.{u}}
    (Z : PrimeDivisor X) : Order.coheight Z.genericPoint = 1 := by
  change Order.coheight ((irreducibleSetEquivPoints (α := X)) Z.support) = 1
  rw [Order.coheight_orderIso, Z.coheight_eq_one]

/-- A unit in the local ring of a prime divisor has vanishing principal coefficient. -/
theorem principalWeilDivisor_coeff_eq_zero_of_isUnit_stalk {X : Scheme.{u}}
    [IsNoetherian X] [IsIntegral X] (f : X.functionFieldˣ) (Z : PrimeDivisor X)
    (a : X.presheaf.stalk Z.genericPoint) (ha : IsUnit a)
    (hfa : algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField a = f) :
    (principalWeilDivisor X f).coeff Z = 0 := by
  rw [principalWeilDivisor_coeff, ← hfa]
  exact ord_eq_zero_of_isUnit_stalk X Z.genericPoint a ha

/-- If a rational function lies in the local ring of a prime divisor, its coefficient is the
length of that local ring modulo the corresponding principal ideal. -/
theorem principalWeilDivisor_coeff_eq_length {X : Scheme.{u}}
    [IsNoetherian X] [IsIntegral X] (f : X.functionFieldˣ) (Z : PrimeDivisor X)
    (a : X.presheaf.stalk Z.genericPoint)
    (hfa : algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField a = f) :
    (principalWeilDivisor X f).coeff Z =
      ((Ring.ord (X.presheaf.stalk Z.genericPoint) a).toNat : ℤ) := by
  have hZ := primeDivisor_genericPoint_coheight Z
  letI : Ring.KrullDimLE 1 (X.presheaf.stalk Z.genericPoint) :=
    krullDimLE_of_coheight_le hZ.le
  have ha : a ≠ 0 := by
    intro ha
    have hf := hfa
    rw [ha, map_zero] at hf
    exact f.ne_zero hf.symm
  rw [principalWeilDivisor_coeff, ← hfa, ord_eq_ordHom_of_coheight_eq_one hZ]
  change Multiplicative.toAdd
    ((Ring.ordFrac (X.presheaf.stalk Z.genericPoint)
      (algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField a)).unzeroD 1) = _
  rw [Ring.ordFrac_eq_ord _ ha,
    Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_of_ne_zero ha)
      (ENat.coe_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero ha))).symm]
  rfl

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
        ((Ring.ord (X.presheaf.stalk Z.genericPoint) b).toNat : ℤ) := by
  let g : X.functionFieldˣ := Units.mk0
    (algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField b) hb
  have ha : algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField a ≠ 0 := by
    intro ha
    rw [ha, zero_div] at hfa
    exact f.ne_zero hfa.symm
  let e : X.functionFieldˣ := Units.mk0
    (algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField a) ha
  have he : e = f * g := by
    apply Units.ext
    exact (div_eq_iff hb).mp hfa
  have hcoeff := congrArg (fun D : Div(X) ↦ D.coeff Z)
    (principalWeilDivisor_mul X f g)
  rw [← he, WeilDivisor.coeff_add,
    principalWeilDivisor_coeff_eq_length e Z a rfl,
    principalWeilDivisor_coeff_eq_length g Z b rfl] at hcoeff
  exact eq_sub_iff_add_eq.mpr hcoeff.symm

end

end AlgebraicGeometry.Scheme
