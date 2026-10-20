/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Positive.IdealPower.Presentation
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication diagrams on ideal-power quotient towers

For a representative `a ∈ I ^ d`, multiplication descends from a later stage of a presented
ideal-power quotient tower to an earlier quotient stage.  The defining transition equation makes
the descended map unique; its restriction supplies maps between the ideal-power terms.  The
resulting successor-row map is exposed for cohomological naturality arguments.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.PNatInverseSystem.IdealPower

variable {A : Type w} [CommRing A]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear A C]

/-- Multiplication maps on a presented ideal-power quotient tower.

For `a ∈ I ^ d`, `stageMap` is the map induced on the quotient by scalar multiplication with
`a`; `termMap` is its restriction to the ideal-power terms. -/
@[stacks 0GYM "multiplication diagrams for an ideal-power quotient tower"]
structure Multiplication
    {I : Ideal A} {F : PNatInverseSystem C} (P : Presentation I F) where
  /-- Multiplication by a representative `a ∈ I ^ d` between ambient tower stages. -/
  stageMap : ∀ d n : ℕ, Ideal.AssociatedGraded.stage I A d →
    (F.stage (Nat.succPNat n) ⟶ F.stage (Nat.succPNat (d + n)))
  /-- The restriction of the ambient multiplication map to ideal-power terms. -/
  termMap : ∀ d n : ℕ, Ideal.AssociatedGraded.stage I A d →
    (terms P n ⟶ terms P (d + n))
  /-- The ambient map is the descent of scalar multiplication along the tower transition. -/
  transition_comp_stageMap : ∀ (d n : ℕ) (a : Ideal.AssociatedGraded.stage I A d),
    F.degreeTransition d n ≫ stageMap d n a = (a : A) • 𝟙 _
  /-- The multiplication map on ideal-power terms is the restriction of the ambient map. -/
  termInclusion_comp_stageMap : ∀ (d n : ℕ) (a : Ideal.AssociatedGraded.stage I A d),
    termInclusion P n ≫ stageMap d n a =
      termMap d n a ≫ termInclusion P (d + n)

/-- Returning to the earlier stage after a multiplication map is scalar multiplication there. -/
theorem Multiplication.stageMap_comp_transition
    {I : Ideal A} {F : PNatInverseSystem C} {P : Presentation I F}
    (μ : Multiplication P) (d n : ℕ)
    (a : Ideal.AssociatedGraded.stage I A d) :
    μ.stageMap d n a ≫ F.degreeTransition d n = (a : A) • 𝟙 _ := sorry

/-- Ambient multiplication maps commute with the successor maps of the positive tower. -/
theorem Multiplication.stageMap_stepMap
    {I : Ideal A} {F : PNatInverseSystem C} {P : Presentation I F}
    (μ : Multiplication P) (d n : ℕ)
    (a : Ideal.AssociatedGraded.stage I A d) :
    μ.stageMap d (n + 1) a ≫ F.stepMap (Nat.succPNat (d + n)) =
      F.stepMap (Nat.succPNat n) ≫ μ.stageMap d n a := sorry

/-- Multiplication by a stage representative as a morphism between the corresponding successor
short exact rows. -/
@[stacks 0GYK "multiplication map between ideal-power quotient rows"]
def Multiplication.stepRowMap
    {I : Ideal A} {F : PNatInverseSystem C} {P : Presentation I F}
    (μ : Multiplication P) (d n : ℕ)
    (a : Ideal.AssociatedGraded.stage I A d) :
    F.stepRow P.positiveTerms P.ι P.isQuotient.comp_zero (Nat.succPNat n) ⟶
      F.stepRow P.positiveTerms P.ι P.isQuotient.comp_zero
        (Nat.succPNat (d + n)) :=
  ShortComplex.homMk
    (μ.termMap d (n + 1) a)
    (μ.stageMap d (n + 1) a)
    (μ.stageMap d n a)
    (μ.termInclusion_comp_stageMap d (n + 1) a).symm
    (μ.stageMap_stepMap d n a)

end CategoryTheory.PNatInverseSystem.IdealPower
