/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Cech.Comparison

/-! Compatibility checks for the covering-simplex Čech API. -/

open CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

universe u v w vS wA

variable {C : Type u} [Category.{v} C]
variable {U X : FiberedCategoryOver.Groupoids C}

#check (CategoryTheory.FiberedCategoryOver.Groupoids.Cech.map :
  ∀ {V Y : FiberedCategoryOver.Groupoids C} {f : U ⟶ X} {g : V ⟶ Y}
    {h : V ⟶ U} {e : Y ⟶ X} (t : h ≫ f ≅ g ≫ e)
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}),
    Cech.complex f F ⟶ Cech.complex g (Cech.inverseImage e F))

#check (CategoryTheory.FiberedCategoryOver.Groupoids.Cech.isoOfTwoIso :
  ∀ {f f' : U ⟶ X} (t : f ≅ f') (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}),
    Cech.complex f F ≅ Cech.complex f' F)
