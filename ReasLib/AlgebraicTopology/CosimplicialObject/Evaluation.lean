/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Evaluation of cosimplicial objects

Mathlib defines `CosimplicialObject` opaquely, so instances attached to ordinary functor-category
evaluation do not automatically elaborate on its public surface. This leaf owns the canonical
evaluation functor and its basic API without exposing that implementation detail downstream.
-/

@[expose] public section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory.CosimplicialObject

/-- Cosimplicial objects inherit zero morphisms pointwise from their target category. -/
@[stacks 018Z "zero morphisms of cosimplicial objects"]
instance hasZeroMorphisms (A : Type u) [Category.{v} A] [HasZeroMorphisms A] :
    HasZeroMorphisms (CosimplicialObject A) :=
  inferInstanceAs (HasZeroMorphisms (SimplexCategory ⥤ A))

/-- Cosimplicial objects inherit their preadditive structure pointwise from the target category. -/
@[stacks 018Z "preadditive structure on cosimplicial objects"]
instance preadditive (A : Type u) [Category.{v} A] [Preadditive A] :
    Preadditive (CosimplicialObject A) :=
  inferInstanceAs (Preadditive (SimplexCategory ⥤ A))

/-- Evaluation of a cosimplicial object at a simplex. -/
@[stacks 018Z "evaluation of cosimplicial objects"]
def evaluation (A : Type u) [Category.{v} A] (Delta : SimplexCategory) :
    CosimplicialObject A ⥤ A :=
  (CategoryTheory.evaluation SimplexCategory A).obj Delta

/-- Cosimplicial evaluation returns the value at the chosen simplex. -/
@[simp, stacks 018Z "cosimplicial evaluation on objects"]
theorem evaluation_obj (A : Type u) [Category.{v} A] (Delta : SimplexCategory)
    (X : CosimplicialObject A) :
    (evaluation A Delta).obj X = X.obj Delta := sorry

/-- Cosimplicial evaluation sends a natural transformation to its chosen component. -/
@[simp, stacks 018Z "cosimplicial evaluation on morphisms"]
theorem evaluation_map (A : Type u) [Category.{v} A] (Delta : SimplexCategory)
    {X Y : CosimplicialObject A} (f : X ⟶ Y) :
    (evaluation A Delta).map f = f.app Delta := sorry

namespace evaluation

/-- Evaluation of cosimplicial objects preserves zero morphisms. -/
@[stacks 018Z "cosimplicial evaluation preserves zero morphisms"]
instance preservesZeroMorphisms (A : Type u) [Category.{v} A] [HasZeroMorphisms A]
    (Delta : SimplexCategory) :
    (evaluation A Delta).PreservesZeroMorphisms := sorry

/-- Evaluation of cosimplicial objects is additive when the target category is preadditive. -/
@[stacks 018Z "cosimplicial evaluation is additive"]
instance additive (A : Type u) [Category.{v} A] [Preadditive A]
    (Delta : SimplexCategory) :
    (evaluation A Delta).Additive := sorry

end evaluation

end CategoryTheory.CosimplicialObject
