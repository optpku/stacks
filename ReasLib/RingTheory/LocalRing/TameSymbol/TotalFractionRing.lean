module

public import ReasLib.RingTheory.LocalRing.TameSymbol.TotalFractionRing.Factorization

@[expose] public section

/-!
# Tame symbols on total fraction rings

The bimultiplicative localization of the integral scalar-quotient determinant agrees with
factorization formulas and satisfies antisymmetry and the Steinberg relation.
-/

noncomputable section

open scoped nonZeroDivisors

universe u v w

namespace TameSymbol.Total

variable (A : Type u) (K : Type v) [CommRing A] [IsLocalRing A]
  [IsNoetherianRing A] [CommRing K] [Algebra A K] [IsFractionRing A K]

/-- On embedded nonzerodivisors, the total tame symbol agrees with every chosen
factorization formula after the canonical residue-field comparison. -/
theorem value_mapNonzero_eq_factorizationValue
    (hdim : ringKrullDim A = 1) {B : Type w} [CommRing B] [Algebra A B]
    [Module.Finite A B] (a b : A⁰)
    (D : TameSymbol.Factorization A B (a : A) (b : A)) :
    Units.map (IsLocalRing.ResidueField.maximalIdealAlgEquiv A).toMonoidHom
        (value A K hdim (mapNonzero A K a) (mapNonzero A K b)) = D.value := sorry

/-- The total tame symbol is multiplicative in its first argument. -/
theorem value_mul_left (hdim : ringKrullDim A = 1) (x₁ x₂ y : Kˣ) :
    value A K hdim (x₁ * x₂) y = value A K hdim x₁ y * value A K hdim x₂ y := sorry

/-- The total tame symbol is multiplicative in its second argument. -/
theorem value_mul_right (hdim : ringKrullDim A = 1) (x y₁ y₂ : Kˣ) :
    value A K hdim x (y₁ * y₂) = value A K hdim x y₁ * value A K hdim x y₂ := sorry

/-- The values obtained by exchanging the two arguments multiply to one. -/
theorem value_mul_swap (hdim : ringKrullDim A = 1) (x y : Kˣ) :
    value A K hdim x y * value A K hdim y x = 1 := sorry

/-- The total tame symbol satisfies the Steinberg relation. -/
theorem value_one_sub (hdim : ringKrullDim A = 1) (x y : Kˣ)
    (hy : (y : K) = 1 - (x : K)) :
    value A K hdim x y = 1 := sorry

end TameSymbol.Total
