module

public import ReasLib.RingTheory.LocalRing.TameSymbol.TotalFractionRing
import StacksCheckRecall

@[expose] public section

open scoped nonZeroDivisors

universe u v w

section

variable (A : Type u) (K : Type v) [CommRing A] [IsLocalRing A]
  [IsNoetherianRing A] [CommRing K] [Algebra A K] [IsFractionRing A K]

/- Lemma 42.5.2 (1): the integral tame symbol extends canonically to a
bimultiplicative map on the units of the fraction field. -/
@[stacks 0EAS] #check (TameSymbol.Total.value A K :
  ringKrullDim A = 1 → Kˣ →* (Kˣ →* (IsLocalRing.ResidueField A)ˣ))

/- Lemma 42.5.2 (2): on integral nonzerodivisors, the extended map agrees
with every factorization formula defining the tame symbol. -/
@[stacks 0EAS] #check
  (TameSymbol.Total.value_mapNonzero_eq_factorizationValue (A := A) (K := K) :
    (hdim : ringKrullDim A = 1) → {B : Type w} → [CommRing B] → [Algebra A B] →
      [Module.Finite A B] → (a b : A⁰) →
      (D : TameSymbol.Factorization A B (a : A) (b : A)) →
        Units.map (IsLocalRing.ResidueField.maximalIdealAlgEquiv A).toMonoidHom
            (TameSymbol.Total.value A K hdim
              (TameSymbol.Total.mapNonzero A K a) (TameSymbol.Total.mapNonzero A K b)) =
          D.value)

/- Lemma 42.5.2 (3): the integral tame symbol is multiplicative in its first
argument. -/
@[stacks 0EAS] #check (TameSymbol.Total.integralValue_mul_left (A := A) :
  (hdim : ringKrullDim A = 1) → (a b c : A⁰) →
    TameSymbol.Total.integralValue A hdim (a * b) c =
      TameSymbol.Total.integralValue A hdim a c *
        TameSymbol.Total.integralValue A hdim b c)

/- Lemma 42.5.2 (4): the integral tame symbol is multiplicative in its second
argument. -/
@[stacks 0EAS] #check (TameSymbol.Total.integralValue_mul_right (A := A) :
  (hdim : ringKrullDim A = 1) → (a b c : A⁰) →
    TameSymbol.Total.integralValue A hdim a (b * c) =
      TameSymbol.Total.integralValue A hdim a b *
        TameSymbol.Total.integralValue A hdim a c)

/- Lemma 42.5.2 (5): on the diagonal, the integral tame symbol is the parity
sign of the principal quotient length. -/
@[stacks 0EAS] #check (TameSymbol.Total.integralValue_same (A := A) :
  (hdim : ringKrullDim A = 1) → (a : A⁰) →
    TameSymbol.Total.integralValue A hdim a a =
      (-1 : (IsLocalRing.ResidueField A)ˣ) ^
        (Module.length A (QuotSMulTop (a : A) A)).toNat)

/- Lemma 42.5.2 (6): with a unit in its first argument, the integral tame
symbol is the corresponding residue raised to the order of the second argument. -/
@[stacks 0EAS] #check (TameSymbol.Total.integralValue_unit (A := A) :
  (hdim : ringKrullDim A = 1) → (a : Aˣ) → (b : A⁰) →
    TameSymbol.Total.integralValue A hdim (TameSymbol.Total.unitNonzero A a) b =
      Units.map (IsLocalRing.residue A).toMonoidHom a ^ (Ring.ord A (b : A)).toNat)

/- Lemma 42.5.2 (7): nonzerodivisors `a`, `b`, and `c = b - a` satisfy the
subtraction cross-product identity. -/
@[stacks 0EAS] #check (TameSymbol.Total.integralValue_sub (A := A) :
  (hdim : ringKrullDim A = 1) → (a b c : A⁰) →
    (c : A) = (b : A) - (a : A) →
      TameSymbol.Total.integralValue A hdim a c *
          TameSymbol.Total.integralValue A hdim b b =
        TameSymbol.Total.integralValue A hdim b c *
          TameSymbol.Total.integralValue A hdim a b)

/- Lemma 42.5.2 (8): the extended tame symbol is multiplicative in its first
argument. -/
@[stacks 0EAS] #check (TameSymbol.Total.value_mul_left (A := A) (K := K) :
  (hdim : ringKrullDim A = 1) → (x₁ x₂ y : Kˣ) →
    TameSymbol.Total.value A K hdim (x₁ * x₂) y =
      TameSymbol.Total.value A K hdim x₁ y * TameSymbol.Total.value A K hdim x₂ y)

/- Lemma 42.5.2 (9): the extended tame symbol is multiplicative in its second
argument. -/
@[stacks 0EAS] #check (TameSymbol.Total.value_mul_right (A := A) (K := K) :
  (hdim : ringKrullDim A = 1) → (x y₁ y₂ : Kˣ) →
    TameSymbol.Total.value A K hdim x (y₁ * y₂) =
      TameSymbol.Total.value A K hdim x y₁ * TameSymbol.Total.value A K hdim x y₂)

/- Lemma 42.5.2 (10): exchanging the arguments of the extended tame symbol
gives inverse values. -/
@[stacks 0EAS] #check (TameSymbol.Total.value_mul_swap (A := A) (K := K) :
  (hdim : ringKrullDim A = 1) → (x y : Kˣ) →
    TameSymbol.Total.value A K hdim x y * TameSymbol.Total.value A K hdim y x = 1)

/- Lemma 42.5.2 (11): the extended tame symbol satisfies the Steinberg
relation. -/
@[stacks 0EAS] #check (TameSymbol.Total.value_one_sub (A := A) (K := K) :
  (hdim : ringKrullDim A = 1) → (x y : Kˣ) →
    (y : K) = 1 - (x : K) → TameSymbol.Total.value A K hdim x y = 1)

end
