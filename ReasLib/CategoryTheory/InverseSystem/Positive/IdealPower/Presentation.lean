module

public import ReasLib.CategoryTheory.InverseSystem.Positive.IdealPower
import Mathlib.Tactic.CrossRefAttribute

/-!
# Presented ideal-power quotient towers

This leaf bundles the positive ideal-power terms, their inclusions, and the short exact quotient
laws for a positive inverse system in an arbitrary linear category.  It also adjoins the canonical
degree-zero term and records the mono/epi facts used by graded multiplication diagrams.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.PNatInverseSystem.IdealPower

variable {A : Type w} [CommRing A]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear A C]

/-- A presentation of a positive tower by the short exact ideal-power rows
`I ^ n • F (n + 1) ⟶ F (n + 1) ⟶ F n`. -/
@[stacks 0GYM "ideal-power presentation of a positive inverse system"]
structure Presentation (I : Ideal A) (F : PNatInverseSystem C) where
  /-- The positive-degree ideal-power terms. -/
  positiveTerms : ℕ+ → C
  /-- The inclusion of each positive-degree ideal-power term. -/
  ι : ∀ n : ℕ+, positiveTerms n ⟶ F.stage (n + 1)
  /-- The inclusions identify the terms with ideal powers and form short exact quotient rows. -/
  isQuotient : F.IsIdealPowerQuotient I positiveTerms ι

/-- The full family of a presented ideal-power tower, with degree zero canonically equal to
`F 1`. -/
@[stacks 0GYM "ideal-power terms for a positive inverse system"]
def terms {I : Ideal A} {F : PNatInverseSystem C}
    (P : Presentation I F) : ℕ → C
  | 0 => F.stage 1
  | n + 1 => P.positiveTerms (Nat.succPNat n)

/-- The degree-zero ideal-power term is the first object of the positive tower. -/
@[simp]
theorem terms_zero {I : Ideal A} {F : PNatInverseSystem C}
    (P : Presentation I F) :
    terms P 0 = F.stage 1 := sorry

/-- Positive degrees of the full family are the presented positive ideal-power terms. -/
@[simp]
theorem terms_succ {I : Ideal A} {F : PNatInverseSystem C}
    (P : Presentation I F) (n : ℕ) :
    terms P (n + 1) = P.positiveTerms (Nat.succPNat n) := sorry

/-- The canonical inclusion of the degree-`n` term into `F (n + 1)`, using the identity in
degree zero. -/
@[stacks 0GYM "inclusion of an ideal-power term into its ambient tower stage"]
def termInclusion {I : Ideal A} {F : PNatInverseSystem C}
    (P : Presentation I F) : ∀ n : ℕ,
      terms P n ⟶ F.stage (Nat.succPNat n)
  | 0 => 𝟙 _
  | n + 1 => P.ι (Nat.succPNat n)

/-- Every ideal-power term inclusion, including the canonical degree-zero inclusion, is monic. -/
theorem Presentation.mono_termInclusion
    {I : Ideal A} {F : PNatInverseSystem C}
    (P : Presentation I F) (n : ℕ) :
    Mono (termInclusion P n) := sorry

/-- Extract the universal-property identification of every positive term in a presentation. -/
theorem Presentation.isSMulSubobject
    {I : Ideal A} {F : PNatInverseSystem C}
    (P : Presentation I F) (n : ℕ+) :
    (I ^ (n : ℕ)).IsSMulSubobject (P.ι n) := sorry

/-- Extract the short exact quotient row at a positive degree of a presentation. -/
theorem Presentation.shortExact
    {I : Ideal A} {F : PNatInverseSystem C}
    (P : Presentation I F) (n : ℕ+) :
    (F.stepRow P.positiveTerms P.ι P.isQuotient.comp_zero n).ShortExact := sorry

/-- Every degree-shifting transition of a presented ideal-power quotient tower is epimorphic. -/
theorem Presentation.epi_degreeTransition
    {I : Ideal A} {F : PNatInverseSystem C}
    (P : Presentation I F) (d n : ℕ) :
    Epi (F.degreeTransition d n) := sorry

end CategoryTheory.PNatInverseSystem.IdealPower
