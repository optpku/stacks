/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.GroupTheory.MonoidLocalization.Maps
public import Mathlib.RingTheory.Localization.FractionRing
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant.Multiplicativity
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant.Subtraction
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant.Swap
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant.UnitAction
public import ReasLib.RingTheory.LocalRing.ResidueField.MaximalIdeal
public import ReasLib.RingTheory.LocalRing.TameSymbol.Factorization.Independence

@[expose] public section

/-!
# Tame symbols on total fraction rings from integral factorizations

The scalar-quotient determinant on nonzerodivisors is extended in each variable along the
group localization presenting the units of a total fraction ring.
-/

noncomputable section

open scoped nonZeroDivisors

universe u v

namespace TameSymbol.Total

/-- A unit of a commutative ring, regarded as a nonzerodivisor. -/
def unitNonzero (A : Type u) [CommRing A] : Aˣ →* A⁰ where
  toFun u := ⟨u, u.isUnit.mem_nonZeroDivisors⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The element underlying a unit regarded as a nonzerodivisor is the original unit. -/
theorem coe_unitNonzero_apply (A : Type u) [CommRing A] (u : Aˣ) :
    (unitNonzero A u : A) = u := sorry

variable (A : Type u) (K : Type v) [CommRing A] [IsLocalRing A]
  [IsNoetherianRing A] [CommRing K] [Algebra A K] [IsFractionRing A K]

/-- The algebra map sends each nonzerodivisor to its canonical unit in a total fraction ring. -/
noncomputable def mapNonzero : A⁰ →* Kˣ :=
  IsUnit.liftRight ((algebraMap A K).toMonoidHom.restrict A⁰) fun a ↦
    IsLocalization.map_units K a

/-- The element underlying the image of a nonzerodivisor is its image under the algebra map. -/
theorem coe_mapNonzero_apply (a : A⁰) :
    (mapNonzero A K a : K) = algebraMap A K a := sorry

/-- The canonical map from nonzerodivisors to fraction-ring units is a group localization. -/
theorem mapNonzero_isLocalizationMap :
    (⊤ : Submonoid A⁰).IsLocalizationMap (mapNonzero A K) := sorry

/-- The units of a total fraction ring as the group localization of the nonzerodivisors. -/
noncomputable def fractionUnits : (⊤ : Submonoid A⁰).LocalizationMap Kˣ where
  __ := mapNonzero A K
  isLocalizationMap := mapNonzero_isLocalizationMap A K

/-- The monoid homomorphism underlying the fraction-unit localization is the canonical map. -/
theorem fractionUnits_toMonoidHom :
    (fractionUnits A K).toMonoidHom = mapNonzero A K := sorry

/-- The integral scalar-quotient determinant is one when its second argument is one. -/
theorem integral_one_right (a : A⁰) (hdim : ringKrullDim A = 1) :
    CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
      (a : A) 1 a.property (one_mem A⁰) hdim = 1 := sorry

/-- The integral scalar-quotient determinant is multiplicative in its second argument. -/
theorem integral_mul_right (a b c : A⁰) (hdim : ringKrullDim A = 1) :
    CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
        (a : A) (b * c : A) a.property (b * c).property hdim =
      CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
          (a : A) (b : A) a.property b.property hdim *
        CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
          (a : A) (c : A) a.property c.property hdim := sorry

/-- The integral scalar-quotient determinant is one when its first argument is one. -/
theorem integral_one_left (b : A⁰) (hdim : ringKrullDim A = 1) :
    CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
      1 (b : A) (one_mem A⁰) b.property hdim = 1 := sorry

/-- The integral scalar-quotient determinant is multiplicative in its first argument. -/
theorem integral_mul_left (a b c : A⁰) (hdim : ringKrullDim A = 1) :
    CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
        (a * b : A) (c : A) (a * b).property c.property hdim =
      CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
          (a : A) (c : A) a.property c.property hdim *
        CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
          (b : A) (c : A) b.property c.property hdim := sorry

/-- With an integral first argument fixed, the scalar-quotient determinant is a homomorphism
in the second nonzerodivisor. -/
noncomputable def integralRight (hdim : ringKrullDim A = 1) (a : A⁰) :
    A⁰ →* (IsLocalRing.ResidueField A)ˣ where
  toFun b := CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
    (a : A) (b : A) a.property b.property hdim
  map_one' := integral_one_right A a hdim
  map_mul' b c := integral_mul_right A a b c hdim

/-- Evaluating the integral right homomorphism gives the scalar-quotient determinant. -/
theorem integralRight_apply (hdim : ringKrullDim A = 1) (a b : A⁰) :
    integralRight A hdim a b =
      CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
        (a : A) (b : A) a.property b.property hdim := sorry

/-- At first argument one, the integral right homomorphism is trivial. -/
theorem integralRight_one (hdim : ringKrullDim A = 1) :
    integralRight A hdim 1 = 1 := sorry

/-- Integral right homomorphisms multiply with their first arguments. -/
theorem integralRight_mul (hdim : ringKrullDim A = 1) (a b : A⁰) :
    integralRight A hdim (a * b) = integralRight A hdim a * integralRight A hdim b := sorry

/-- The scalar-quotient determinant as a bimultiplicative map on nonzerodivisors. -/
noncomputable def integralValue (hdim : ringKrullDim A = 1) :
    A⁰ →* (A⁰ →* (IsLocalRing.ResidueField A)ˣ) where
  toFun := integralRight A hdim
  map_one' := integralRight_one A hdim
  map_mul' := integralRight_mul A hdim

/-- Evaluating the integral tame symbol gives the scalar-quotient determinant. -/
theorem integralValue_apply (hdim : ringKrullDim A = 1) (a b : A⁰) :
    integralValue A hdim a b =
      CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
        (a : A) (b : A) a.property b.property hdim := sorry

/-- The integral tame symbol is multiplicative in its first argument. -/
theorem integralValue_mul_left (hdim : ringKrullDim A = 1) (a b c : A⁰) :
    integralValue A hdim (a * b) c =
      integralValue A hdim a c * integralValue A hdim b c := sorry

/-- The integral tame symbol is multiplicative in its second argument. -/
theorem integralValue_mul_right (hdim : ringKrullDim A = 1) (a b c : A⁰) :
    integralValue A hdim a (b * c) =
      integralValue A hdim a b * integralValue A hdim a c := sorry

/-- On the diagonal, the integral tame symbol is the parity sign of the principal quotient
length. -/
theorem integralValue_same (hdim : ringKrullDim A = 1) (a : A⁰) :
    integralValue A hdim a a =
      (-1 : (IsLocalRing.ResidueField A)ˣ) ^
        (Module.length A (QuotSMulTop (a : A) A)).toNat := sorry

/-- With a unit in the first argument, the integral tame symbol is its residue raised to the
order of the second argument. -/
theorem integralValue_unit (hdim : ringKrullDim A = 1) (u : Aˣ) (b : A⁰) :
    integralValue A hdim (unitNonzero A u) b =
      Units.map (IsLocalRing.residue A).toMonoidHom u ^ (Ring.ord A (b : A)).toNat := sorry

/-- For nonzerodivisors `a`, `b`, and `c = b - a`, the integral tame symbols satisfy the
subtraction cross-product identity. -/
theorem integralValue_sub (hdim : ringKrullDim A = 1) (a b c : A⁰)
    (hc : (c : A) = (b : A) - (a : A)) :
    integralValue A hdim a c * integralValue A hdim b b =
      integralValue A hdim b c * integralValue A hdim a b := sorry

/-- Extension of the integral tame symbol in its second variable to fraction-ring units. -/
noncomputable def extendRight (hdim : ringKrullDim A = 1) (a : A⁰) :
    Kˣ →* (IsLocalRing.ResidueField A)ˣ :=
  (fractionUnits A K).lift fun b : (⊤ : Submonoid A⁰) ↦
    Group.isUnit (integralValue A hdim a b)

/-- The right extension agrees with the integral tame symbol on nonzerodivisors. -/
theorem extendRight_mapNonzero (hdim : ringKrullDim A = 1) (a b : A⁰) :
    extendRight A K hdim a (mapNonzero A K b) = integralValue A hdim a b := sorry

/-- At integral first argument one, the right extension is trivial. -/
theorem extendRight_one (hdim : ringKrullDim A = 1) :
    extendRight A K hdim 1 = 1 := sorry

/-- Right extensions multiply with their integral first arguments. -/
theorem extendRight_mul (hdim : ringKrullDim A = 1) (a b : A⁰) :
    extendRight A K hdim (a * b) = extendRight A K hdim a * extendRight A K hdim b := sorry

/-- The right-extended determinant as a homomorphism in its integral first argument. -/
noncomputable def integralExtension (hdim : ringKrullDim A = 1) :
    A⁰ →* (Kˣ →* (IsLocalRing.ResidueField A)ˣ) where
  toFun := extendRight A K hdim
  map_one' := extendRight_one A K hdim
  map_mul' := extendRight_mul A K hdim

/-- Evaluating the integral extension in its first argument gives the right extension. -/
theorem integralExtension_apply (hdim : ringKrullDim A = 1) (a : A⁰) :
    integralExtension A K hdim a = extendRight A K hdim a := sorry

/-- The tame symbol, obtained by extending the integral determinant multiplicatively in both
variables to the units of a total fraction ring. -/
noncomputable def value (hdim : ringKrullDim A = 1) :
    Kˣ →* (Kˣ →* (IsLocalRing.ResidueField A)ˣ) :=
  (fractionUnits A K).lift fun a : (⊤ : Submonoid A⁰) ↦
    Group.isUnit (integralExtension A K hdim a)

/-- The total tame symbol agrees with the integral tame symbol on nonzerodivisors. -/
theorem value_mapNonzero (hdim : ringKrullDim A = 1) (a b : A⁰) :
    value A K hdim (mapNonzero A K a) (mapNonzero A K b) =
      integralValue A hdim a b := sorry

/-- The value on two fractions is the alternating product of the four integral values of
their numerators and denominators. -/
theorem value_fraction (hdim : ringKrullDim A = 1) (x y : Kˣ)
    (a₁ a₂ b₁ b₂ : A⁰)
    (hx : x * mapNonzero A K a₂ = mapNonzero A K a₁)
    (hy : y * mapNonzero A K b₂ = mapNonzero A K b₁) :
    value A K hdim x y =
      integralValue A hdim a₁ b₁ * (integralValue A hdim a₁ b₂)⁻¹ *
        (integralValue A hdim a₂ b₁)⁻¹ * integralValue A hdim a₂ b₂ := sorry

/-- A bimultiplicative map agreeing with the integral scalar-quotient determinant is the
total tame symbol. -/
theorem value_unique (hdim : ringKrullDim A = 1)
    (f : Kˣ →* (Kˣ →* (IsLocalRing.ResidueField A)ˣ))
    (hf : ∀ a b : A⁰,
      f (mapNonzero A K a) (mapNonzero A K b) =
        CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
          (a : A) (b : A) a.property b.property hdim) :
    f = value A K hdim := sorry

end TameSymbol.Total
