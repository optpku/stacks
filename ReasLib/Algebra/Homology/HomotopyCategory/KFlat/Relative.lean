/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import ReasLib.Algebra.Homology.HomologicalComplex.KFlat.Relative
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative K-flat objects in the homotopy category

This file specializes bifunctor-relative K-flatness to homotopy-category objects while retaining
independent shapes for the source complex, representative complex, and total complex.
@stack 06XZ
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w

namespace CategoryTheory.HomotopyCategory

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D]
  [HasZeroMorphisms C₁] [Preadditive C₂] [Preadditive D]
variable {I₁ : Type w₁} {I₂ : Type w₂} {J : Type w}
  {c₂ : ComplexShape I₂}

/-- A homotopy-category object is K-flat for a bifunctor when its representative complex is
K-flat for that bifunctor and the chosen source and total shapes. -/
@[stacks 06XZ "bifunctor-relative homotopy-category form"]
abbrev IsKFlatFor (K : HomotopyCategory C₂ c₂) (F : C₁ ⥤ C₂ ⥤ D)
    (c₁ : ComplexShape I₁) (c : ComplexShape J)
    [TotalComplexShape c₁ c₂ c] [DecidableEq J]
    [F.PreservesZeroMorphisms] [∀ X : C₁, (F.obj X).PreservesZeroMorphisms] : Prop :=
  HomologicalComplex.IsKFlatFor K.as F c₁ c

/-- Relative K-flatness of a homotopy-category object is relative K-flatness of its
representative complex. -/
theorem isKFlatFor_iff (K : HomotopyCategory C₂ c₂) (F : C₁ ⥤ C₂ ⥤ D)
    (c₁ : ComplexShape I₁) (c : ComplexShape J)
    [TotalComplexShape c₁ c₂ c] [DecidableEq J]
    [F.PreservesZeroMorphisms] [∀ X : C₁, (F.obj X).PreservesZeroMorphisms] :
    K.IsKFlatFor F c₁ c ↔ HomologicalComplex.IsKFlatFor K.as F c₁ c := sorry

end CategoryTheory.HomotopyCategory
