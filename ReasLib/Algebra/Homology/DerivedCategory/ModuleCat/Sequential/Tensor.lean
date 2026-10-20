/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sequential.Monoidal
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Sequential.Evaluation
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Sequential.Resolution
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Braiding
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Bifunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived tensor products of sequential varying-ring modules

@stack 091H

Stagewise K-flat representatives supply the canonical unbounded derived tensor product on a
sequential varying-ring module category.  The generic `DerivedTensor` API owns the tensor object,
its symmetry, and exactness in each variable; this leaf installs only the varying-ring existence
and evaluation-compatibility facts.
-/

@[expose] public section

open CategoryTheory ComplexShape Opposite

noncomputable section

universe u

namespace CategoryTheory.SequentialInverseSystem.ModuleSystem

-- Local instance justification (defeq pin): the K-flat existence statements use the standard
-- derived-category localizations on the varying-ring module category and on every stage.
attribute [local instance] HasDerivedCategory.standard

/-- Lemma 15.88.9 (091H) (1): sequential varying-ring modules admit canonical fixed-left and
fixed-right unbounded derived tensor functors. -/
@[stacks 091H "(1) derived tensor existence"]
instance hasDerivedTensor (F : SequentialInverseSystem CommRingCat.{u}) :
    DerivedCategory.DerivedTensor.Has (C := ModuleSystem.{u, u} F) := sorry

/-- The tensor bifunctor on sequential varying-ring modules admits a total left-derived bifunctor
in both variables. -/
@[stacks 091H "(1) two-variable derived tensor existence"]
instance hasDerivedTensorBifunctor (F : SequentialInverseSystem CommRingCat.{u}) :
    DerivedCategory.DerivedTensor.Bifunctor.Has
      (C := ModuleSystem.{u, u} F) := sorry

/-- The canonical two-variable model agrees with the fixed-right derived tensor after one input
is fixed. -/
@[stacks 091H "fixed-right and two-variable tensor compatibility"]
instance derivedTensorBifunctorRightCompatible
    (F : SequentialInverseSystem CommRingCat.{u})
    (E : DerivedCategory (ModuleSystem.{u, u} F)) :
    DerivedCategory.DerivedTensor.Bifunctor.Right.Compatible E := sorry

/-- Lemma 15.88.9 (091H) (2): derived tensor product is compatible with evaluation at every
stage of the varying-ring system. -/
@[stacks 091H "(2) evaluation compatibility"]
theorem derivedEvaluationTensor_isomorphic
    (F : SequentialInverseSystem CommRingCat.{u}) (n : Nat)
    (K L : DerivedCategory (ModuleSystem.{u, u} F)) :
    IsIsomorphic
      ((derivedEvaluation F n).obj (DerivedCategory.DerivedTensor.Right.obj K L))
      (DerivedCategory.DerivedTensor.Right.obj
        ((derivedEvaluation F n).obj K) ((derivedEvaluation F n).obj L)) := sorry

/-- Lemma 15.88.9 (091H) (4): derived tensoring with a fixed right factor is exact in the
triangulated sense. -/
@[stacks 091H "(4) fixed-right exactness"]
theorem derivedTensorRight_isTriangulated
    (F : SequentialInverseSystem CommRingCat.{u})
    (L : DerivedCategory (ModuleSystem.{u, u} F)) :
    (DerivedCategory.DerivedTensor.Right.functor L).IsTriangulated := sorry

/-- Lemma 15.88.9 (091H) (4): derived tensoring with a fixed left factor is exact in the
triangulated sense. -/
@[stacks 091H "(4) fixed-left exactness"]
theorem derivedTensorLeft_isTriangulated
    (F : SequentialInverseSystem CommRingCat.{u})
    (K : DerivedCategory (ModuleSystem.{u, u} F)) :
    (DerivedCategory.DerivedTensor.Left.functor K).IsTriangulated := sorry

end CategoryTheory.SequentialInverseSystem.ModuleSystem
