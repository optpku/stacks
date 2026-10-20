/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Diagram
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Pretriangulated.TriangleMorphism.Pro
public import ReasLib.CategoryTheory.Pro.Value
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Essential constancy in sequential systems of distinguished triangles

In a sequential system of distinguished triangles, essential constancy of the outer vertex
systems produces a distinguished triangle of values and forces essential constancy of the middle
vertex system.
-/

@[expose] public section

open CategoryTheory Limits Opposite
open CategoryTheory.Pretriangulated
open scoped CategoryTheory ZeroObject

universe u v

namespace CategoryTheory.Pro.Sequential.Distinguished.EssentiallyConstant

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- Lemma 13.42.2 (Stacks 0G3A) (1): essentially constant outer systems in a sequential system
of distinguished triangles admit a distinguished triangle of values and a stage map representing
all three Hom-colimits. -/
@[stacks 0G3A]
theorem existsStageRepresentative
    {T : SequentialInverseSystem (Triangle D)}
    (hT : ∀ n : ℕ, T.obj (op n) ∈ distTriang D)
    (h₁ : IsCofiltered.IsEssentiallyConstant (T ⋙ Triangle.π₁))
    (h₃ : IsCofiltered.IsEssentiallyConstant (T ⋙ Triangle.π₃)) :
    ∃ (U : Triangle D) (n : ℕ) (φ : T.obj (op (n + 1)) ⟶ U),
      U ∈ distTriang D ∧
        Pretriangulated.TriangleMorphism.IsHomColimitRepresentative φ := sorry

/-- Lemma 13.42.2 (Stacks 0G3A) (2): a sequential system of distinguished triangles with
essentially constant outer systems has a distinguished triangle of pro-values for all three
vertices. -/
@[stacks 0G3A]
theorem existsValueTriangle
    {T : SequentialInverseSystem (Triangle D)}
    (hT : ∀ n : ℕ, T.obj (op n) ∈ distTriang D)
    (h₁ : IsCofiltered.IsEssentiallyConstant (T ⋙ Triangle.π₁))
    (h₃ : IsCofiltered.IsEssentiallyConstant (T ⋙ Triangle.π₃)) :
    ∃ U : Triangle D, U ∈ distTriang D ∧
      HasValue (T ⋙ Triangle.π₁) U.obj₁ ∧
      HasValue (T ⋙ Triangle.π₂) U.obj₂ ∧
      HasValue (T ⋙ Triangle.π₃) U.obj₃ := sorry

/-- Lemma 13.42.2 (Stacks 0G3A) (3): the middle vertex of a sequential system of distinguished
triangles is essentially constant when the outer vertices are essentially constant. -/
@[stacks 0G3A]
theorem middle
    {T : SequentialInverseSystem (Triangle D)}
    (hT : ∀ n : ℕ, T.obj (op n) ∈ distTriang D)
    (h₁ : IsCofiltered.IsEssentiallyConstant (T ⋙ Triangle.π₁))
    (h₃ : IsCofiltered.IsEssentiallyConstant (T ⋙ Triangle.π₃)) :
    IsCofiltered.IsEssentiallyConstant (T ⋙ Triangle.π₂) := sorry

end CategoryTheory.Pro.Sequential.Distinguished.EssentiallyConstant
