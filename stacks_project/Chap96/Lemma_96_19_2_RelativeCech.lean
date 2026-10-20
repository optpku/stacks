/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.RelativeCech.Complex

/-! Compatibility check for the relative Čech complex. -/

open CategoryTheory Functor FiberedCategoryOver.Groupoids FiberedCategoryOver.Groupoids.Cech
open scoped Bicategory Simplicial

universe u v wA

variable {C : Type u} [Category.{v} C]
variable {U X : FiberedCategoryOver.Groupoids C}

#check (CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech.complex :
  ∀ (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (reindex φ).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f m).op) G],
    CochainComplex (X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) ℕ)
