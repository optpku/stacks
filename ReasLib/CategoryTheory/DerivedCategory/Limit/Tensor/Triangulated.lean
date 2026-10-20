/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.DerivedFunctor.Triangulated
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Tensor

@[expose] public section

/-!
# Triangulated Tensor-Derived-Limit Functors

@stack 08U1

This leaf records shift and distinguished-triangle APIs for the fixed-factor
tensor-derived-limit composites.
-/

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
open ComplexShape

noncomputable section

universe wA wSys v u

namespace CategoryTheory.DerivedLimit

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]
variable [MonoidalPreadditive (SequentialInverseSystem A)]
variable [∀ (K L : CochainComplex (SequentialInverseSystem A) ℤ),
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (SequentialInverseSystem A)) (up ℤ)]
variable [HasLimitsOfShape ℕᵒᵖ A]
variable [(lim : SequentialInverseSystem A ⥤ A).Additive]
variable [HasDerivedFunctor A]

/-- The fixed-right-factor tensor-derived-limit functor commutes with shifts
when its tensor and derived-limit models provide the comparisons. -/
@[stacks 08U1, stacks 091J "fixed-right tensor derived limit commutes with shifts"]
noncomputable instance tensorRight_commShift
    (E : DerivedCategory (SequentialInverseSystem A))
    [DerivedCategory.DerivedTensor.Right.Has (C := SequentialInverseSystem A)]
    [TriangulatedModel A] : (tensorRight E).CommShift ℤ := inferInstance

/-- The fixed-right-factor tensor-derived-limit functor is triangulated when
its tensor and derived-limit models are triangulated. -/
@[stacks 08U1, stacks 091J "fixed-right tensor derived limit is triangulated"]
instance tensorRight_isTriangulated
    (E : DerivedCategory (SequentialInverseSystem A))
    [DerivedCategory.DerivedTensor.Right.Has (C := SequentialInverseSystem A)]
    [TriangulatedModel A] : (tensorRight E).IsTriangulated := inferInstance

/-- The fixed-left-factor tensor-derived-limit functor commutes with shifts
when its tensor and derived-limit models provide the comparisons. -/
@[stacks 08U1, stacks 091K "fixed-left tensor derived limit commutes with shifts"]
noncomputable instance tensorLeft_commShift
    (K : DerivedCategory A)
    [DerivedCategory.DerivedTensor.Left.Has (C := SequentialInverseSystem A)]
    [TriangulatedModel A] : (tensorLeft K).CommShift ℤ := inferInstance

/-- The fixed-left-factor tensor-derived-limit functor is triangulated when
its tensor and derived-limit models are triangulated. -/
@[stacks 08U1, stacks 091K "fixed-left tensor derived limit is triangulated"]
instance tensorLeft_isTriangulated
    (K : DerivedCategory A)
    [DerivedCategory.DerivedTensor.Left.Has (C := SequentialInverseSystem A)]
    [TriangulatedModel A] : (tensorLeft K).IsTriangulated := inferInstance

/-- A fixed-right-factor tensor-derived-limit functor sends distinguished
triangles to distinguished triangles. -/
@[stacks 08U1 "fixed-right tensor derived limit preserves distinguished triangles"]
theorem tensorRight_map_distinguished
    (E : DerivedCategory (SequentialInverseSystem A))
    [DerivedCategory.DerivedTensor.Right.Has (C := SequentialInverseSystem A)]
    [TriangulatedModel A] (T : Triangle (DerivedCategory A))
    (hT : T ∈ distTriang (DerivedCategory A)) :
    (tensorRight E).mapTriangle.obj T ∈ distTriang (DerivedCategory A) := sorry

/-- A fixed-left-factor tensor-derived-limit functor sends distinguished
triangles to distinguished triangles. -/
@[stacks 08U1, stacks 091K "fixed-left tensor derived limit preserves distinguished triangles"]
theorem tensorLeft_map_distinguished
    (K : DerivedCategory A)
    [DerivedCategory.DerivedTensor.Left.Has (C := SequentialInverseSystem A)]
    [TriangulatedModel A] (T : Triangle (DerivedCategory (SequentialInverseSystem A)))
    (hT : T ∈ distTriang (DerivedCategory (SequentialInverseSystem A))) :
    (tensorLeft K).mapTriangle.obj T ∈ distTriang (DerivedCategory A) := sorry

end CategoryTheory.DerivedLimit
