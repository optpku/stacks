module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.GroupTheory.MonoidLocalization.Maps
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant.Multiplicativity
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant.Swap

@[expose] public section

/-!
# The tame symbol of a one-dimensional Noetherian local domain

The integral determinant is extended in each variable from the nonzerodivisors of the
domain to the units of an arbitrary chosen fraction field.
-/

noncomputable section

open scoped nonZeroDivisors

universe u v

namespace TameSymbol

variable (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
  [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K]

/-- The algebra map sends nonzerodivisors of `A` canonically to units of its fraction field
`K`. -/
noncomputable def mapNonzero : A⁰ →* Kˣ :=
  (nonZeroDivisorsEquivUnits : K⁰ ≃* Kˣ).toMonoidHom.comp <|
    ((algebraMap A K).toMonoidHom.restrict A⁰).codRestrict K⁰ fun a ↦
      map_mem_nonZeroDivisors (algebraMap A K) (IsFractionRing.injective A K) a.property

/-- The underlying element of `mapNonzero A K a` is the image of `a` in `K`. -/
theorem coe_mapNonzero_apply (a : A⁰) :
    (mapNonzero A K a : K) = algebraMap A K a := sorry

/-- The map from the nonzerodivisors of `A` to `Kˣ` exhibits the latter as their group
localization. -/
theorem mapNonzero_isLocalizationMap :
    (⊤ : Submonoid A⁰).IsLocalizationMap (mapNonzero A K) := sorry

/-- The group-localization map from the nonzerodivisors of `A` to the units of `K`. -/
noncomputable def fractionUnits : (⊤ : Submonoid A⁰).LocalizationMap Kˣ where
  __ := mapNonzero A K
  isLocalizationMap := mapNonzero_isLocalizationMap A K

/-- The monoid homomorphism underlying `fractionUnits A K` is `mapNonzero A K`. -/
theorem fractionUnits_toMonoidHom :
    (fractionUnits A K).toMonoidHom = mapNonzero A K := sorry

/-- The integral determinant has value one when its second argument is one. -/
theorem integral_one_right (a : A⁰) (hdim : ringKrullDim A = 1) :
    CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
      (a : A) 1 a.property (one_mem A⁰) hdim = 1 := sorry

/-- The integral determinant is multiplicative in its second argument. -/
theorem integral_mul_right (a b c : A⁰) (hdim : ringKrullDim A = 1) :
    CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
        (a : A) (b * c : A) a.property (b * c).property hdim =
      CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
          (a : A) (b : A) a.property b.property hdim *
        CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
          (a : A) (c : A) a.property c.property hdim := sorry

/-- The integral determinant has value one when its first argument is one. -/
theorem integral_one_left (b : A⁰) (hdim : ringKrullDim A = 1) :
    CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
      1 (b : A) (one_mem A⁰) b.property hdim = 1 := sorry

/-- The integral determinant is multiplicative in its first argument. -/
theorem integral_mul_left (a b c : A⁰) (hdim : ringKrullDim A = 1) :
    CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
        (a * b : A) (c : A) (a * b).property c.property hdim =
      CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
          (a : A) (c : A) a.property c.property hdim *
        CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
          (b : A) (c : A) b.property c.property hdim := sorry

/-- For an integral first argument, the integral determinant as a homomorphism in its second
argument. -/
noncomputable def integralRight (hdim : ringKrullDim A = 1) (a : A⁰) :
    A⁰ →* (IsLocalRing.ResidueField A)ˣ where
  toFun b := CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
    (a : A) (b : A) a.property b.property hdim
  map_one' := integral_one_right A a hdim
  map_mul' b c := integral_mul_right A a b c hdim

/-- Evaluating `integralRight` recovers the integral scalar-quotient determinant. -/
theorem integralRight_apply (hdim : ringKrullDim A = 1) (a b : A⁰) :
    integralRight A hdim a b =
      CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
        (a : A) (b : A) a.property b.property hdim := sorry

/-- At first argument one, `integralRight` is the trivial homomorphism. -/
theorem integralRight_one (hdim : ringKrullDim A = 1) :
    integralRight A hdim 1 = 1 := sorry

/-- The family `integralRight` is multiplicative in its integral first argument. -/
theorem integralRight_mul (hdim : ringKrullDim A = 1) (a b : A⁰) :
    integralRight A hdim (a * b) =
      integralRight A hdim a * integralRight A hdim b := sorry

/-- The scalar-quotient determinant as a bimultiplicative map on the nonzerodivisors of `A`. -/
noncomputable def integralValue (hdim : ringKrullDim A = 1) :
    A⁰ →* (A⁰ →* (IsLocalRing.ResidueField A)ˣ) where
  toFun := integralRight A hdim
  map_one' := integralRight_one A hdim
  map_mul' := integralRight_mul A hdim

/-- Evaluating `integralValue` recovers the integral scalar-quotient determinant. -/
theorem integralValue_apply (hdim : ringKrullDim A = 1) (a b : A⁰) :
    integralValue A hdim a b =
      CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
        (a : A) (b : A) a.property b.property hdim := sorry

/-- Extension of the integral determinant in the second variable to `Kˣ`. -/
noncomputable def extendRight (hdim : ringKrullDim A = 1) (a : A⁰) :
    Kˣ →* (IsLocalRing.ResidueField A)ˣ :=
  (fractionUnits A K).lift fun b : (⊤ : Submonoid A⁰) ↦
    Group.isUnit (integralValue A hdim a b)

/-- The right extension agrees with the integral determinant on nonzerodivisors. -/
theorem extendRight_mapNonzero (hdim : ringKrullDim A = 1) (a b : A⁰) :
    extendRight A K hdim a (mapNonzero A K b) =
      CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
        (a : A) (b : A) a.property b.property hdim := sorry

/-- At integral first argument one, the right extension is the trivial homomorphism. -/
theorem extendRight_one (hdim : ringKrullDim A = 1) :
    extendRight A K hdim 1 = 1 := sorry

/-- The right extensions are multiplicative in their integral first argument. -/
theorem extendRight_mul (hdim : ringKrullDim A = 1) (a b : A⁰) :
    extendRight A K hdim (a * b) =
      extendRight A K hdim a * extendRight A K hdim b := sorry

/-- The right-extended determinant as a homomorphism in its integral first argument. -/
noncomputable def integralExtension (hdim : ringKrullDim A = 1) :
    A⁰ →* (Kˣ →* (IsLocalRing.ResidueField A)ˣ) where
  toFun := extendRight A K hdim
  map_one' := extendRight_one A K hdim
  map_mul' := extendRight_mul A K hdim

/-- Evaluating `integralExtension` in its first argument gives `extendRight`. -/
theorem integralExtension_apply (hdim : ringKrullDim A = 1) (a : A⁰) :
    integralExtension A K hdim a = extendRight A K hdim a := sorry

/-- The tame symbol, obtained by extending the integral determinant multiplicatively in both
variables to the units of `K`. -/
noncomputable def value (hdim : ringKrullDim A = 1) :
    Kˣ →* (Kˣ →* (IsLocalRing.ResidueField A)ˣ) :=
  (fractionUnits A K).lift fun a : (⊤ : Submonoid A⁰) ↦
    Group.isUnit (integralExtension A K hdim a)

/-- The tame symbol agrees with the scalar-quotient determinant on integral nonzerodivisors. -/
theorem value_mapNonzero (hdim : ringKrullDim A = 1) (a b : A⁰) :
    value A K hdim (mapNonzero A K a) (mapNonzero A K b) =
      CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
        (a : A) (b : A) a.property b.property hdim := sorry

/-- A bimultiplicative map on `Kˣ` that agrees with the integral determinant on all
nonzerodivisors is the tame symbol. -/
theorem value_unique (hdim : ringKrullDim A = 1)
    (f : Kˣ →* (Kˣ →* (IsLocalRing.ResidueField A)ˣ))
    (hf : ∀ a b : A⁰,
      f (mapNonzero A K a) (mapNonzero A K b) =
        CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
          (a : A) (b : A) a.property b.property hdim) :
    f = value A K hdim := sorry

end TameSymbol
