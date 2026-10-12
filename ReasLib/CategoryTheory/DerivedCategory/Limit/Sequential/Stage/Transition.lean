/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.DerivedCategory.FunctorCategory.DerivedEvaluation.Map
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Stage

@[expose] public section

/-!
# Transitions Between Derived Stages

This module derives the transition between any two comparable evaluation
stages. Successor maps are exposed as specializations for tower construction.
@stack 0CQD
-/

open CategoryTheory

noncomputable section

universe wA wSys u v

namespace CategoryTheory.DerivedLimit.Stage

variable (A : Type u) [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]

/-- The transition from stage `j` to stage `i` for `i ≤ j`. -/
@[stacks 0CQD]
abbrev transition {i j : ℕ} (h : i ≤ j) : evaluation A j ⟶ evaluation A i :=
  (_root_.CategoryTheory.evaluation ℕᵒᵖ A).map ((homOfLE h).op)

/-- The cochain-level natural transformation induced by a stage transition. -/
@[stacks 0CQD]
abbrev cochainTransition {i j : ℕ} (h : i ≤ j) :
    cochainEvaluation A j ⟶ cochainEvaluation A i :=
  FunctorCategory.DerivedEvaluation.cochainMap ℕᵒᵖ A ((homOfLE h).op)

/-- The right-derived natural transformation induced by a stage transition. -/
@[stacks 0CQD]
abbrev derivedTransition {i j : ℕ} (h : i ≤ j) :
    derivedEvaluation A j ⟶ derivedEvaluation A i :=
  FunctorCategory.DerivedEvaluation.derivedMap ℕᵒᵖ A ((homOfLE h).op)

/-- The successor transition between consecutive stage-evaluation functors. -/
abbrev step (n : ℕ) : evaluation A (n + 1) ⟶ evaluation A n :=
  transition A (Nat.le_succ n)

/-- The cochain-level successor transition. -/
abbrev cochainStep (n : ℕ) :
    cochainEvaluation A (n + 1) ⟶ cochainEvaluation A n :=
  cochainTransition A (Nat.le_succ n)

/-- The right-derived successor transition. -/
abbrev derivedStep (n : ℕ) :
    derivedEvaluation A (n + 1) ⟶ derivedEvaluation A n :=
  derivedTransition A (Nat.le_succ n)

end CategoryTheory.DerivedLimit.Stage
