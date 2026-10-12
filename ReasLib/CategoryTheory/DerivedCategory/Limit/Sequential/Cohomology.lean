/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.Cohomology
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.HomotopyLimit.Grothendieck
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cohomology of the Canonical Sequential Derived Limit

@stack 0CQE

This leaf specializes the Milnor cohomology short exact sequence to the canonical total right
derived inverse-limit functor and its stagewise tower.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w wA wSys u v

namespace CategoryTheory.DerivedLimit

variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]
variable [IsGrothendieckAbelian.{w} A]
variable [IsGrothendieckAbelian.{w} (SequentialInverseSystem A)]
variable [HasLimitsOfShape ℕᵒᵖ A]
variable [HasCountableProducts A] [CountableAB4Star A]
variable [PreservesLimitsOfShape (Discrete ℕ) (lim : SequentialInverseSystem A ⥤ A)]

/-- Lemma 15.88.4 (Stacks 0CQE): the cohomology of the canonical total right derived inverse
limit fits into the Milnor short exact sequence for the stagewise tower. -/
@[stacks 0CQE]
theorem cohomologyShortExact
    (K : DerivedCategory (SequentialInverseSystem A)) (p : ℤ) :
    ∃ (ι : R1
        (Stage.tower K ⋙ DerivedCategory.homologyFunctor A (p - 1)) ⟶
        cohomology K p)
      (π : cohomology K p ⟶
        limit (Stage.tower K ⋙ DerivedCategory.homologyFunctor A p))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

end CategoryTheory.DerivedLimit
