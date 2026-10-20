/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Cech.Simplex

/-! Compatibility checks for the covering-simplex Čech API. -/

open CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

universe u v w vS wA

variable {C : Type u} [Category.{v} C]
variable {U X : FiberedCategoryOver.Groupoids C}

#check (CategoryTheory.FiberedCategoryOver.Groupoids.Cech.covering :
  (f : U ⟶ X) → SimplexCategory → FiberedCategoryOver.Groupoids C)

#check (CategoryTheory.FiberedCategoryOver.Groupoids.Cech.reindex :
  ∀ {f : U ⟶ X} {m n : SimplexCategory}, (m ⟶ n) →
    Cech.Simplex.Obj f n ⥤ Cech.Simplex.Obj f m)

#check (CategoryTheory.FiberedCategoryOver.Groupoids.Cech.degreeZeroTo :
  (f : U ⟶ X) → U ⟶ Cech.covering f ⦋0⦌)
