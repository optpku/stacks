/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.Product

/-!
# Binary products of categories fibred in groupoids

The shared product-representability theorem is checked here over an arbitrary base category.
-/

@[expose] public section

open CategoryTheory
open scoped Bicategory

universe u v

variable {C : Type u} [Category.{v} C]
variable {X₁ X₂ Y₁ Y₂ : FiberedCategoryOver.Groupoids.{u, v, max u v, v} C}

#check (CategoryTheory.FiberedCategoryOver.Groupoids.relativelyRepresentable.prod_map :
  ∀ {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂},
    FiberedCategoryOver.Groupoids.relativelyRepresentable f₁ →
    FiberedCategoryOver.Groupoids.relativelyRepresentable f₂ →
    FiberedCategoryOver.Groupoids.relativelyRepresentable
      (FiberedCategoryOver.Groupoids.prodMap f₁ f₂))
