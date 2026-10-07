module

public import ReasLib.CategoryTheory.InverseSystem.Positive.ShortComplex
public import ReasLib.CategoryTheory.Linear.Ideal.Subobject
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ideal-power terms in positive inverse systems

This file records, through the universal property of `Ideal.IsSMulSubobject`, that the kernel term
at positive stage `n` really is `I ^ n • F (n + 1)`.  It is independent of sheaves and
cohomology.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.PNatInverseSystem

variable {A : Type w} [CommRing A]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear A C]

/-- A compatible family presents its positive terms as the ideal powers
`I ^ n • F (n + 1)`. -/
@[stacks 0GYM "ideal-power terms in a positive inverse system"]
def IsIdealPowerTerms
    (F : PNatInverseSystem C) (I : Ideal A) (K : ℕ+ → C)
    (ι : ∀ n : ℕ+, K n ⟶ F.stage (n + 1)) : Prop :=
  ∀ n : ℕ+, (I ^ (n : ℕ)).IsSMulSubobject (ι n)

/-- Extract the universal property of one ideal-power term. -/
theorem IsIdealPowerTerms.isSMulSubobject
    {F : PNatInverseSystem C} {I : Ideal A} {K : ℕ+ → C}
    {ι : ∀ n : ℕ+, K n ⟶ F.stage (n + 1)}
    (h : F.IsIdealPowerTerms I K ι) (n : ℕ+) :
    (I ^ (n : ℕ)).IsSMulSubobject (ι n) := sorry

/-- A positive inverse system is successively obtained by quotienting `F (n + 1)` by its
canonical ideal-power term `I ^ n • F (n + 1)`. -/
@[stacks 0GYM "positive inverse system of ideal-power quotients"]
def IsIdealPowerQuotient
    (F : PNatInverseSystem C) (I : Ideal A) (K : ℕ+ → C)
    (ι : ∀ n : ℕ+, K n ⟶ F.stage (n + 1)) : Prop :=
  F.IsIdealPowerTerms I K ι ∧
    ∃ hι : ∀ n : ℕ+, ι n ≫ F.stepMap n = 0,
      F.IsStepShortExact K ι hι

/-- An ideal-power quotient tower has the correct ideal-power kernel terms. -/
theorem IsIdealPowerQuotient.terms
    {F : PNatInverseSystem C} {I : Ideal A} {K : ℕ+ → C}
    {ι : ∀ n : ℕ+, K n ⟶ F.stage (n + 1)}
    (h : F.IsIdealPowerQuotient I K ι) :
    F.IsIdealPowerTerms I K ι := sorry

/-- The inclusion of an ideal-power term is killed by the corresponding quotient map. -/
theorem IsIdealPowerQuotient.comp_zero
    {F : PNatInverseSystem C} {I : Ideal A} {K : ℕ+ → C}
    {ι : ∀ n : ℕ+, K n ⟶ F.stage (n + 1)}
    (h : F.IsIdealPowerQuotient I K ι) (n : ℕ+) :
    ι n ≫ F.stepMap n = 0 := sorry

/-- Every successor row of an ideal-power quotient tower is short exact. -/
theorem IsIdealPowerQuotient.shortExact
    {F : PNatInverseSystem C} {I : Ideal A} {K : ℕ+ → C}
    {ι : ∀ n : ℕ+, K n ⟶ F.stage (n + 1)}
    (h : F.IsIdealPowerQuotient I K ι) (n : ℕ+) :
    (F.stepRow K ι h.comp_zero n).ShortExact := sorry

end CategoryTheory.PNatInverseSystem
