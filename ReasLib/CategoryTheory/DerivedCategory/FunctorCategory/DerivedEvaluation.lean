/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived Evaluation on Functor Categories

Evaluation at an object of an indexing category is exact, hence induces a
functor between the corresponding derived categories. This module owns that
construction independently of any particular diagram shape.
@stack 0CQD
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe wD wA vJ uJ vA uA

namespace CategoryTheory.FunctorCategory.DerivedEvaluation

variable (J : Type uJ) [Category.{vJ} J]
variable (A : Type uA) [Category.{vA} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wD} (J ⥤ A)]

/-- Exact evaluation at `j` transported to derived categories. -/
@[stacks 0CQD]
abbrev functor (j : J) : DerivedCategory (J ⥤ A) ⥤ DerivedCategory A :=
  ((_root_.CategoryTheory.evaluation J A).obj j).mapDerivedCategory

/-- Evaluation at `j` on cochain complexes, followed by localization. -/
@[stacks 0CQD]
abbrev cochainFunctor (j : J) :
    CochainComplex (J ⥤ A) ℤ ⥤ DerivedCategory A :=
  ((_root_.CategoryTheory.evaluation J A).obj j).mapHomologicalComplex (up ℤ) ⋙
    (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)

/-- The canonical cochain-level comparison unit for derived evaluation. -/
@[stacks 0CQD]
noncomputable abbrev unit (j : J) :
    cochainFunctor J A j ⟶
      (DerivedCategory.Q :
          CochainComplex (J ⥤ A) ℤ ⥤ DerivedCategory (J ⥤ A)) ⋙
        functor J A j :=
  ((_root_.CategoryTheory.evaluation J A).obj j).mapDerivedCategoryFactors.inv

end CategoryTheory.FunctorCategory.DerivedEvaluation
