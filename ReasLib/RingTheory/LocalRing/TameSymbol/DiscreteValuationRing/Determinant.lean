module

public import Mathlib.GroupTheory.MonoidLocalization.Maps
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant
public import ReasLib.RingTheory.LocalRing.TameSymbol.DiscreteValuationRing.Formula

@[expose] public section

/-!
# Determinant construction of the tame symbol of a discrete valuation ring

The scalar-quotient determinant on nonzerodivisors is extended multiplicatively in both
variables to the units of an arbitrary fraction field of a discrete valuation ring.
-/

noncomputable section

open scoped nonZeroDivisors

universe u v

namespace DVR.TameSymbol

variable (A : Type u) (K : Type v) [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]

/-- The map from the nonzerodivisors of a discrete valuation ring to the units of its
fraction field is their group localization. -/
theorem mapNonzero_isLocalizationMap :
    (⊤ : Submonoid A⁰).IsLocalizationMap (mapNonzero A K) := sorry

/-- The group-localization map from the nonzerodivisors of a discrete valuation ring to
the units of its fraction field. -/
noncomputable def fractionUnits : (⊤ : Submonoid A⁰).LocalizationMap Kˣ where
  __ := mapNonzero A K
  isLocalizationMap := mapNonzero_isLocalizationMap A K

/-- The monoid homomorphism underlying `fractionUnits A K` is `mapNonzero A K`. -/
theorem fractionUnits_toMonoidHom :
    (fractionUnits A K).toMonoidHom = mapNonzero A K := sorry

/-- The integral scalar-quotient determinant has value one when its second argument is one. -/
theorem integral_one_right (a : A⁰) :
    CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
      (a : A) 1 a.property (one_mem A⁰)
        (IsDiscreteValuationRing.ringKrullDim_eq_one A) = 1 := sorry

/-- The integral scalar-quotient determinant is multiplicative in its second argument. -/
theorem integral_mul_right (a b c : A⁰) :
    CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
        (a : A) (b * c : A) a.property (b * c).property
          (IsDiscreteValuationRing.ringKrullDim_eq_one A) =
      CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
          (a : A) (b : A) a.property b.property
            (IsDiscreteValuationRing.ringKrullDim_eq_one A) *
        CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
          (a : A) (c : A) a.property c.property
            (IsDiscreteValuationRing.ringKrullDim_eq_one A) := sorry

/-- The integral scalar-quotient determinant has value one when its first argument is one. -/
theorem integral_one_left (b : A⁰) :
    CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
      1 (b : A) (one_mem A⁰) b.property
        (IsDiscreteValuationRing.ringKrullDim_eq_one A) = 1 := sorry

/-- The integral scalar-quotient determinant is multiplicative in its first argument. -/
theorem integral_mul_left (a b c : A⁰) :
    CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
        (a * b : A) (c : A) (a * b).property c.property
          (IsDiscreteValuationRing.ringKrullDim_eq_one A) =
      CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
          (a : A) (c : A) a.property c.property
            (IsDiscreteValuationRing.ringKrullDim_eq_one A) *
        CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
          (b : A) (c : A) b.property c.property
            (IsDiscreteValuationRing.ringKrullDim_eq_one A) := sorry

/-- For an integral first argument, the scalar-quotient determinant as a homomorphism in
its second argument. -/
noncomputable def integralRight (a : A⁰) : A⁰ →* (IsLocalRing.ResidueField A)ˣ where
  toFun b := CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
    (a : A) (b : A) a.property b.property
      (IsDiscreteValuationRing.ringKrullDim_eq_one A)
  map_one' := integral_one_right A a
  map_mul' b c := integral_mul_right A a b c

/-- Evaluating `integralRight` recovers the integral scalar-quotient determinant. -/
theorem integralRight_apply (a b : A⁰) :
    integralRight A a b =
      CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
        (a : A) (b : A) a.property b.property
          (IsDiscreteValuationRing.ringKrullDim_eq_one A) := sorry

/-- At first argument one, `integralRight` is the trivial homomorphism. -/
theorem integralRight_one : integralRight A 1 = 1 := sorry

/-- The family `integralRight` is multiplicative in its integral first argument. -/
theorem integralRight_mul (a b : A⁰) :
    integralRight A (a * b) = integralRight A a * integralRight A b := sorry

/-- The scalar-quotient determinant as a bimultiplicative map on the nonzerodivisors. -/
noncomputable def integralValue : A⁰ →* (A⁰ →* (IsLocalRing.ResidueField A)ˣ) where
  toFun := integralRight A
  map_one' := integralRight_one A
  map_mul' := integralRight_mul A

/-- Evaluating `integralValue` recovers the integral scalar-quotient determinant. -/
theorem integralValue_apply (a b : A⁰) :
    integralValue A a b =
      CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
        (a : A) (b : A) a.property b.property
          (IsDiscreteValuationRing.ringKrullDim_eq_one A) := sorry

/-- The integral determinant extended in the second variable to the fraction-field units. -/
noncomputable def extendRight (a : A⁰) : Kˣ →* (IsLocalRing.ResidueField A)ˣ :=
  (fractionUnits A K).lift fun b : (⊤ : Submonoid A⁰) ↦
    Group.isUnit (integralValue A a b)

/-- The right extension agrees with the scalar-quotient determinant on nonzerodivisors. -/
theorem extendRight_mapNonzero (a b : A⁰) :
    extendRight A K a (mapNonzero A K b) =
      CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
        (a : A) (b : A) a.property b.property
          (IsDiscreteValuationRing.ringKrullDim_eq_one A) := sorry

/-- At integral first argument one, the right extension is the trivial homomorphism. -/
theorem extendRight_one : extendRight A K 1 = 1 := sorry

/-- The right extensions are multiplicative in their integral first argument. -/
theorem extendRight_mul (a b : A⁰) :
    extendRight A K (a * b) = extendRight A K a * extendRight A K b := sorry

/-- The right-extended determinant as a homomorphism in its integral first argument. -/
noncomputable def integralExtension : A⁰ →* (Kˣ →* (IsLocalRing.ResidueField A)ˣ) where
  toFun := extendRight A K
  map_one' := extendRight_one A K
  map_mul' := extendRight_mul A K

/-- Evaluating `integralExtension` in its first argument gives `extendRight`. -/
theorem integralExtension_apply (a : A⁰) :
    integralExtension A K a = extendRight A K a := sorry

/-- The determinant tame symbol, obtained by extending the integral scalar-quotient
determinant multiplicatively in both variables. -/
noncomputable def determinantValue : Kˣ →* (Kˣ →* (IsLocalRing.ResidueField A)ˣ) :=
  (fractionUnits A K).lift fun a : (⊤ : Submonoid A⁰) ↦
    Group.isUnit (integralExtension A K a)

/-- The determinant tame symbol agrees with the scalar-quotient determinant on
nonzerodivisors. -/
theorem determinantValue_mapNonzero (a b : A⁰) :
    determinantValue A K (mapNonzero A K a) (mapNonzero A K b) =
      CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
        (a : A) (b : A) a.property b.property
          (IsDiscreteValuationRing.ringKrullDim_eq_one A) := sorry

/-- A bimultiplicative map on the fraction-field units that agrees with the integral
scalar-quotient determinants is the determinant tame symbol. -/
theorem determinantValue_unique
    (f : Kˣ →* (Kˣ →* (IsLocalRing.ResidueField A)ˣ))
    (hf : ∀ a b : A⁰,
      f (mapNonzero A K a) (mapNonzero A K b) =
        CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
          (a : A) (b : A) a.property b.property
            (IsDiscreteValuationRing.ringKrullDim_eq_one A)) :
    f = determinantValue A K := sorry

/-- The explicit tame symbol agrees on integral nonzerodivisors with the scalar-quotient
determinant. -/
theorem value_mapNonzero (a b : A⁰) :
    value A K (mapNonzero A K a) (mapNonzero A K b) =
      CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
        (a : A) (b : A) a.property b.property
          (IsDiscreteValuationRing.ringKrullDim_eq_one A) := sorry

/-- The determinant construction of the tame symbol equals its signed-ratio formula. -/
theorem determinant_eq_value (x y : Kˣ) :
    determinantValue A K x y = value A K x y := sorry

end DVR.TameSymbol
