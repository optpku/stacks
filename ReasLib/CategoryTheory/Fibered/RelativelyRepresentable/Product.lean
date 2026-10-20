/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Product
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange

/-!
# Products of relatively representable morphisms

Relative representability of morphisms between categories fibred in groupoids is stable under
binary products over their common base.
-/

@[expose] public section

open CategoryTheory
open scoped Bicategory

universe u v

namespace CategoryTheory.FiberedCategoryOver.Groupoids

variable {C : Type u} [Category.{v} C]
variable {X₁ X₂ Y₁ Y₂ : FiberedCategoryOver.Groupoids.{u, v, max u v, v} C}

/-- Relative representability of 1-morphisms of categories fibred in groupoids is stable under
binary products. -/
theorem relativelyRepresentable.prod_map {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
    (hf₁ : relativelyRepresentable f₁) (hf₂ : relativelyRepresentable f₂) :
    relativelyRepresentable (prodMap f₁ f₂) := sorry

end CategoryTheory.FiberedCategoryOver.Groupoids
