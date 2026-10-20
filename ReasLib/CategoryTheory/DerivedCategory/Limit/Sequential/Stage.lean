module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.DerivedCategory.FunctorCategory.DerivedEvaluation
public import ReasLib.CategoryTheory.InverseSystem.Sequential

@[expose] public section

/-!
# Stage Evaluation for Derived Sequential Inverse Systems

@stack 0CQD

This module specializes the generic functor-category derived-evaluation API
to sequential inverse systems. It does not depend on a model for derived
inverse limit or on pro-objects.
-/

open CategoryTheory
open Opposite

noncomputable section

universe wA wSys u v

namespace CategoryTheory.DerivedLimit.Stage

variable (A : Type u) [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]

/-- Evaluation at the `n`th stage of a sequential inverse system. -/
@[stacks 0CQD]
abbrev evaluation (n : ℕ) : SequentialInverseSystem A ⥤ A :=
  (_root_.CategoryTheory.evaluation ℕᵒᵖ A).obj (op n)

/-- Evaluation at stage `n` transported to derived categories. -/
@[stacks 0CQD]
abbrev derivedEvaluation (n : ℕ) :
    DerivedCategory (SequentialInverseSystem A) ⥤ DerivedCategory A :=
  FunctorCategory.DerivedEvaluation.functor ℕᵒᵖ A (op n)

/-- Evaluation at stage `n` on cochain complexes, followed by localization. -/
@[stacks 0CQD]
abbrev cochainEvaluation (n : ℕ) :
    CochainComplex (SequentialInverseSystem A) ℤ ⥤ DerivedCategory A :=
  FunctorCategory.DerivedEvaluation.cochainFunctor ℕᵒᵖ A (op n)

/-- The canonical cochain-level comparison unit for derived stage evaluation. -/
@[stacks 0CQD]
noncomputable abbrev unit (n : ℕ) :
    cochainEvaluation A n ⟶
      (DerivedCategory.Q :
        CochainComplex (SequentialInverseSystem A) ℤ ⥤
          DerivedCategory (SequentialInverseSystem A)) ⋙
        derivedEvaluation A n :=
  FunctorCategory.DerivedEvaluation.unit ℕᵒᵖ A (op n)

end CategoryTheory.DerivedLimit.Stage
