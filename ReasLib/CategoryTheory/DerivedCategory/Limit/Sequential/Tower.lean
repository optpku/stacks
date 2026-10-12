/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.DerivedCategory.FunctorCategory.DerivedEvaluation.Diagram
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Stage

@[expose] public section

/-!
# The Stagewise Tower of a Derived Sequential Inverse System

@stack 0CQD

This module packages derived stage evaluation into a functorial sequential
inverse system. It is independent of derived inverse limit and pro-objects.
-/

open CategoryTheory

noncomputable section

universe wA wSys u v

namespace CategoryTheory.DerivedLimit.Stage

variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]

/-- Stacks 0CQD: the sequential tower obtained by evaluating a derived
inverse-system object stagewise. -/
@[stacks 0CQD]
abbrev tower (K : DerivedCategory (SequentialInverseSystem A)) :
    SequentialInverseSystem (DerivedCategory A) :=
  (FunctorCategory.DerivedEvaluation.diagramFunctor ℕᵒᵖ A).obj K

/-- Stacks 0CQD: stagewise derived evaluation is functorial in the derived
inverse-system object. -/
@[stacks 0CQD]
noncomputable abbrev towerFunctor (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{wA} A]
    [HasDerivedCategory.{wSys} (SequentialInverseSystem A)] :
    DerivedCategory (SequentialInverseSystem A) ⥤
      SequentialInverseSystem (DerivedCategory A) :=
  FunctorCategory.DerivedEvaluation.diagramFunctor ℕᵒᵖ A

end CategoryTheory.DerivedLimit.Stage
