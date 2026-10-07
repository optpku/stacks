module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

@[expose] public section

/-!
# The tame symbol of a discrete valuation ring

This module constructs the usual tame symbol on the units of an arbitrary fraction field of a
discrete valuation ring. Its value is obtained by reducing the signed valuation-zero ratio in the
residue field.
-/

noncomputable section

open IsDedekindDomain
open scoped nonZeroDivisors WithZero

universe u v

namespace DVR.TameSymbol

variable (A : Type u) (K : Type v) [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]

/-- The additive order attached to the maximal-ideal valuation of a discrete valuation ring. -/
noncomputable def ord (x : Kˣ) : ℤ :=
  -WithZero.log (((IsDiscreteValuationRing.maximalIdeal A).valuation K) (x : K))

/-- The additive order sends products to sums. -/
theorem ord_mul (x y : Kˣ) : ord A K (x * y) = ord A K x + ord A K y := sorry

/-- The additive order negates under inversion. -/
theorem ord_inv (x : Kˣ) : ord A K x⁻¹ = -ord A K x := sorry

/-- The algebra map sends nonzerodivisors of `A` canonically to units of `K`. -/
noncomputable def mapNonzero : A⁰ →* Kˣ :=
  (nonZeroDivisorsEquivUnits : K⁰ ≃* Kˣ).toMonoidHom.comp <|
    ((algebraMap A K).toMonoidHom.restrict A⁰).codRestrict K⁰ fun a ↦
      map_mem_nonZeroDivisors (algebraMap A K) (IsFractionRing.injective A K) a.property

/-- The underlying element of `mapNonzero A K a` is the image of `a` under `algebraMap A K`. -/
theorem coe_mapNonzero_apply (a : A⁰) :
    (mapNonzero A K a : K) = algebraMap A K a := sorry

/-- The signed valuation-zero ratio whose residue is the tame symbol. -/
def signedRatio (x y : Kˣ) : Kˣ :=
  (-1 : Kˣ) ^ (ord A K x * ord A K y) * x ^ ord A K y / y ^ ord A K x

/-- The signed ratio is explicitly the sign times the quotient with crossed orders. -/
theorem signedRatio_apply (x y : Kˣ) :
    signedRatio A K x y =
      (-1 : Kˣ) ^ (ord A K x * ord A K y) * x ^ ord A K y / y ^ ord A K x := sorry

/-- The signed ratio has multiplicative valuation one. -/
theorem signedRatio_valuation (x y : Kˣ) :
    ((IsDiscreteValuationRing.maximalIdeal A).valuation K) (signedRatio A K x y : K) = 1 := sorry

/-- The signed ratio belongs to the unit group of the maximal-ideal valuation subring. -/
theorem signedRatio_mem_unitGroup (x y : Kˣ) :
    signedRatio A K x y ∈
      ((IsDiscreteValuationRing.maximalIdeal A).valuation K).valuationSubring.unitGroup := sorry

/-- The canonical equivalence from the DVR to its maximal-ideal valuation subring. -/
noncomputable def valuationSubringEquiv :
    A ≃+* ((IsDiscreteValuationRing.maximalIdeal A).valuation K).valuationSubring :=
  IsDiscreteValuationRing.equivValuationSubring

/-- Reduction from the unit group of the maximal-ideal valuation subring to the residue-field
units of `A`. -/
noncomputable def residueUnit :
    ((IsDiscreteValuationRing.maximalIdeal A).valuation K).valuationSubring.unitGroup →*
      (IsLocalRing.ResidueField A)ˣ :=
  (Units.map
    (IsLocalRing.ResidueField.mapEquiv
      (valuationSubringEquiv A K)).symm.toMonoidHom).comp
      (((IsDiscreteValuationRing.maximalIdeal A).valuation K).valuationSubring
        |>.unitGroupToResidueFieldUnits)

/-- Transporting a reduced unit forward to the valuation subring recovers its canonical residue. -/
theorem residueUnit_apply
    (z : ((IsDiscreteValuationRing.maximalIdeal A).valuation K).valuationSubring.unitGroup) :
    Units.map
        (IsLocalRing.ResidueField.mapEquiv
          (valuationSubringEquiv A K)).toMonoidHom
        (residueUnit A K z) =
      (((IsDiscreteValuationRing.maximalIdeal A).valuation K).valuationSubring
        |>.unitGroupToResidueFieldUnits) z := sorry

/-- The signed ratio, packaged as a unit of the maximal-ideal valuation subring. -/
noncomputable def signedRatioUnit (x y : Kˣ) :
    ((IsDiscreteValuationRing.maximalIdeal A).valuation K).valuationSubring.unitGroup :=
  ⟨signedRatio A K x y, signedRatio_mem_unitGroup A K x y⟩

/-- Forgetting the valuation-subring membership of `signedRatioUnit` gives `signedRatio`. -/
theorem coe_signedRatioUnit (x y : Kˣ) :
    (signedRatioUnit A K x y : Kˣ) = signedRatio A K x y := sorry

/-- The residue of the signed valuation-zero ratio. -/
noncomputable def rawValue (x y : Kˣ) : (IsLocalRing.ResidueField A)ˣ :=
  residueUnit A K (signedRatioUnit A K x y)

/-- The raw tame-symbol value is multiplicative in its first argument. -/
theorem rawValue_mul_left (x₁ x₂ y : Kˣ) :
    rawValue A K (x₁ * x₂) y = rawValue A K x₁ y * rawValue A K x₂ y := sorry

/-- The raw tame-symbol value sends one in its first argument to one. -/
theorem rawValue_one_left (y : Kˣ) : rawValue A K 1 y = 1 := sorry

/-- The raw tame-symbol value is multiplicative in its second argument. -/
theorem rawValue_mul_right (x y₁ y₂ : Kˣ) :
    rawValue A K x (y₁ * y₂) = rawValue A K x y₁ * rawValue A K x y₂ := sorry

/-- The raw tame-symbol value sends one in its second argument to one. -/
theorem rawValue_one_right (x : Kˣ) : rawValue A K x 1 = 1 := sorry

/-- For fixed first argument, the tame symbol is a homomorphism in the second argument. -/
noncomputable def valueRight (x : Kˣ) : Kˣ →* (IsLocalRing.ResidueField A)ˣ where
  toFun := rawValue A K x
  map_one' := rawValue_one_right A K x
  map_mul' := rawValue_mul_right A K x

/-- At first argument one, `valueRight` is the trivial homomorphism. -/
theorem valueRight_one : valueRight A K 1 = 1 := sorry

/-- The family `valueRight` is multiplicative in its first argument. -/
theorem valueRight_mul (x₁ x₂ : Kˣ) :
    valueRight A K (x₁ * x₂) = valueRight A K x₁ * valueRight A K x₂ := sorry

/-- The usual tame symbol of a discrete valuation ring, as a bimultiplicative map. -/
noncomputable def value : Kˣ →* (Kˣ →* (IsLocalRing.ResidueField A)ˣ) where
  toFun := valueRight A K
  map_one' := valueRight_one A K
  map_mul' := valueRight_mul A K

/-- The tame symbol evaluates to the residue of the signed valuation-zero ratio. -/
theorem value_apply (x y : Kˣ) : value A K x y = rawValue A K x y := sorry

end DVR.TameSymbol
