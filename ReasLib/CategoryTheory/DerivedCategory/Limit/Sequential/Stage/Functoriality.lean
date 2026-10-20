/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.FunctorCategory.DerivedEvaluation.Functoriality
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Stage.Transition

@[expose] public section

/-!
# Functoriality of Derived Stage Transitions

This leaf records identity and composition laws for stage transitions at the
underived, cochain, and derived levels. The orientation agrees with
`SequentialInverseSystem.transitionMap_comp`.
-/

open CategoryTheory

noncomputable section

universe wA wSys u v

namespace CategoryTheory.DerivedLimit.Stage

namespace transition

variable (A : Type u) [Category.{v} A]

/-- The stage transition attached to a reflexive inequality is the identity. -/
@[simp]
theorem refl (i : ℕ) :
    transition A (le_refl i) = 𝟙 (evaluation A i) := sorry

/-- Stage transitions compose through every intermediate stage. -/
theorem comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    transition A (Nat.le_trans hij hjk) =
      transition A hjk ≫ transition A hij := sorry

end transition

namespace cochainTransition

variable (A : Type u) [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]

/-- The cochain stage transition attached to a reflexive inequality is the identity. -/
@[simp]
theorem refl (i : ℕ) :
    cochainTransition A (le_refl i) = 𝟙 (cochainEvaluation A i) := sorry

/-- Cochain stage transitions compose through every intermediate stage. -/
theorem comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    cochainTransition A (Nat.le_trans hij hjk) =
      cochainTransition A hjk ≫ cochainTransition A hij := sorry

end cochainTransition

namespace derivedTransition

variable (A : Type u) [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]

/-- The derived stage transition attached to a reflexive inequality is the identity. -/
@[simp]
theorem refl (i : ℕ) :
    derivedTransition A (le_refl i) = 𝟙 (derivedEvaluation A i) := sorry

/-- Derived stage transitions compose through every intermediate stage. -/
theorem comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    derivedTransition A (Nat.le_trans hij hjk) =
      derivedTransition A hjk ≫ derivedTransition A hij := sorry

end derivedTransition

end CategoryTheory.DerivedLimit.Stage
