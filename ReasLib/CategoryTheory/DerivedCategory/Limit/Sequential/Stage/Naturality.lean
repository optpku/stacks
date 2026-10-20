/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.FunctorCategory.DerivedEvaluation.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Stage.Transition

@[expose] public section

/-!
# Naturality of Derived Stage Transitions

This leaf exposes the universal-property square defining every derived stage
transition, together with its successor specialization. Identity and
composition laws live in `Stage.Functoriality`.
-/

open CategoryTheory

noncomputable section

universe wA wSys u v

namespace CategoryTheory.DerivedLimit.Stage

variable (A : Type u) [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]

namespace derivedTransition

/-- A derived stage transition is characterized by compatibility with its
two stage-evaluation units. -/
theorem unit_fac {i j : ℕ} (h : i ≤ j) :
    unit A j ≫
        Functor.whiskerLeft
          (DerivedCategory.Q :
            CochainComplex (SequentialInverseSystem A) ℤ ⥤
              DerivedCategory (SequentialInverseSystem A))
          (derivedTransition A h) =
      cochainTransition A h ≫ unit A i := sorry

/-- Component form of `unit_fac` at a cochain complex. -/
@[reassoc]
theorem unit_app {i j : ℕ} (h : i ≤ j)
    (K : CochainComplex (SequentialInverseSystem A) ℤ) :
    (unit A j).app K ≫
        (derivedTransition A h).app
          ((DerivedCategory.Q :
            CochainComplex (SequentialInverseSystem A) ℤ ⥤
              DerivedCategory (SequentialInverseSystem A)).obj K) =
      (cochainTransition A h).app K ≫ (unit A i).app K := sorry

end derivedTransition

namespace derivedStep

/-- The successor specialization of `derivedTransition.unit_fac`. -/
theorem unit_fac (n : ℕ) :
    unit A (n + 1) ≫
        Functor.whiskerLeft
          (DerivedCategory.Q :
            CochainComplex (SequentialInverseSystem A) ℤ ⥤
              DerivedCategory (SequentialInverseSystem A))
          (derivedStep A n) =
      cochainStep A n ≫ unit A n := sorry

/-- Component form of the successor unit square. -/
@[reassoc]
theorem unit_app (n : ℕ) (K : CochainComplex (SequentialInverseSystem A) ℤ) :
    (unit A (n + 1)).app K ≫
        (derivedStep A n).app
          ((DerivedCategory.Q :
            CochainComplex (SequentialInverseSystem A) ℤ ⥤
              DerivedCategory (SequentialInverseSystem A)).obj K) =
      (cochainStep A n).app K ≫ (unit A n).app K := sorry

end derivedStep

end CategoryTheory.DerivedLimit.Stage
