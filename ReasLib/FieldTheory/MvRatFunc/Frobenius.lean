/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Rational functions over a Frobenius-image subfield

Power substitution embeds the prime-field rational function field into itself.
Partial derivatives over its image are defined by the quotient rule.
-/

public section

noncomputable section

namespace MvRatFunc.Frobenius

/-- The rational function field in `n` variables over `ZMod p`. -/
abbrev functionField (n p : ℕ) [Fact p.Prime] : Type :=
  FractionRing (MvPolynomial (Fin n) (ZMod p))

/-- The fraction-field endomorphism induced by substitution of each variable by its
`p`th power. -/
def expandFraction (n p : ℕ) [Fact p.Prime] :
    functionField n p →+* functionField n p :=
  let substitution :=
    (MvPolynomial.expand p :
      MvPolynomial (Fin n) (ZMod p) →ₐ[ZMod p] MvPolynomial (Fin n) (ZMod p)).toRingHom
  IsLocalization.map (functionField n p) substitution
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective substitution
      (MvPolynomial.expand_injective (Nat.Prime.pos Fact.out)))

/-- Power substitution sends each rational-function variable to its `p`th power. -/
theorem expandFraction_X (n p : ℕ) [Fact p.Prime] (index : Fin n) :
    expandFraction n p
        (algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
          (MvPolynomial.X index)) =
      algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
        (MvPolynomial.X index) ^ p := sorry

/-- The image subfield of power substitution on the rational function field. -/
@[expose]
def baseSubfield (n p : ℕ) [Fact p.Prime] : Subfield (functionField n p) :=
  (expandFraction n p).fieldRange

/-- The field of rational functions in the `p`th powers of the variables. -/
abbrev baseField (n p : ℕ) [Fact p.Prime] : Type := baseSubfield n p

/-- A coordinate of the rational function field over the prime field. -/
@[expose]
def coordinate (n p : ℕ) [Fact p.Prime] (index : Fin n) : functionField n p :=
  algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) (MvPolynomial.X index)

/-- The image of a coordinate under power substitution, viewed in the image subfield. -/
@[expose]
def baseCoordinate (n p : ℕ) [Fact p.Prime] (index : Fin n) : baseField n p :=
  (expandFraction n p).rangeRestrictField (coordinate n p index)

/-- The inclusion of the power-substitution image sends its variable generators to
the `p`th powers of the ambient variables. -/
theorem algebraMap_X (n p : ℕ) [Fact p.Prime] (index : Fin n) :
    algebraMap (baseField n p) (functionField n p)
        ((expandFraction n p).rangeRestrictField
          (algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
            (MvPolynomial.X index))) =
      algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
        (MvPolynomial.X index) ^ p := sorry

/-- The rational function field is finite over the subfield of `p`th powers. -/
instance finite (n p : ℕ) [Fact p.Prime] :
    Module.Finite (baseField n p) (functionField n p) := sorry

/-- The quotient-rule expression for the partial derivative of a rational function,
computed from a chosen polynomial numerator and denominator. -/
private def pderivValue (n p : ℕ) [Fact p.Prime] (index : Fin n)
    (value : functionField n p) : functionField n p :=
  let numerator := (IsFractionRing.div_surjective (MvPolynomial (Fin n) (ZMod p)) value).choose
  let denominator :=
    (IsFractionRing.div_surjective (MvPolynomial (Fin n) (ZMod p)) value).choose_spec.choose
  (algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
      (MvPolynomial.pderiv index numerator) *
      algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) denominator -
    algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) numerator *
      algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
        (MvPolynomial.pderiv index denominator)) /
    algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) denominator ^ 2

/-- The quotient-rule value agrees with every polynomial fraction representation
having a nonzero denominator. -/
private theorem pderivValue_div (n p : ℕ) [Fact p.Prime] (index : Fin n)
    (numerator denominator : MvPolynomial (Fin n) (ZMod p))
    (h_denominator : denominator ≠ 0) :
    pderivValue n p index
        (algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) numerator /
          algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) denominator) =
      (algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
          (MvPolynomial.pderiv index numerator) *
          algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) denominator -
        algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) numerator *
          algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
            (MvPolynomial.pderiv index denominator)) /
        algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) denominator ^ 2 := sorry

/-- The quotient-rule partial derivative is additive. -/
private theorem pderivValue_add (n p : ℕ) [Fact p.Prime] (index : Fin n)
    (left right : functionField n p) :
    pderivValue n p index (left + right) =
      pderivValue n p index left + pderivValue n p index right := sorry

/-- The quotient-rule partial derivative is linear over the power-substitution image. -/
private theorem pderivValue_smul (n p : ℕ) [Fact p.Prime] (index : Fin n)
    (scalar : baseField n p) (value : functionField n p) :
    pderivValue n p index (scalar • value) = scalar • pderivValue n p index value := sorry

/-- The quotient-rule partial derivative vanishes at one. -/
private theorem pderivValue_one (n p : ℕ) [Fact p.Prime] (index : Fin n) :
    pderivValue n p index 1 = 0 := sorry

/-- The quotient-rule partial derivative satisfies the Leibniz rule. -/
private theorem pderivValue_mul (n p : ℕ) [Fact p.Prime] (index : Fin n)
    (left right : functionField n p) :
    pderivValue n p index (left * right) =
      left • pderivValue n p index right + right • pderivValue n p index left := sorry

/-- The partial derivative of rational functions in a specified variable, relative
to the subfield of `p`th powers. -/
def pderiv (n p : ℕ) [Fact p.Prime] (index : Fin n) :
    Derivation (baseField n p) (functionField n p) (functionField n p) where
  toFun := pderivValue n p index
  map_add' := pderivValue_add n p index
  map_smul' := pderivValue_smul n p index
  map_one_eq_zero' := pderivValue_one n p index
  leibniz' := pderivValue_mul n p index

/-- The relative partial derivative satisfies the quotient rule for every polynomial
numerator and nonzero polynomial denominator. -/
theorem pderiv_div (n p : ℕ) [Fact p.Prime] (index : Fin n)
    (numerator denominator : MvPolynomial (Fin n) (ZMod p))
    (h_denominator : denominator ≠ 0) :
    pderiv n p index
        (algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) numerator /
          algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) denominator) =
      (algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
          (MvPolynomial.pderiv index numerator) *
          algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) denominator -
        algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) numerator *
          algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
            (MvPolynomial.pderiv index denominator)) /
        algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) denominator ^ 2 := sorry

/-- The rational-function partial derivative extends the polynomial partial derivative. -/
theorem pderiv_algebraMap (n p : ℕ) [Fact p.Prime] (index : Fin n)
    (polynomial : MvPolynomial (Fin n) (ZMod p)) :
    pderiv n p index
        (algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) polynomial) =
      algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
        (MvPolynomial.pderiv index polynomial) := sorry

/-- The partial derivative of its own variable is one. -/
theorem pderiv_X (n p : ℕ) [Fact p.Prime] (index : Fin n) :
    pderiv n p index
        (algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
          (MvPolynomial.X index)) = 1 := sorry

/-- The partial derivative vanishes on each other variable. -/
theorem pderiv_X_of_ne (n p : ℕ) [Fact p.Prime] {index other : Fin n}
    (h_ne : other ≠ index) :
    pderiv n p index
        (algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
          (MvPolynomial.X other)) = 0 := sorry

end MvRatFunc.Frobenius
