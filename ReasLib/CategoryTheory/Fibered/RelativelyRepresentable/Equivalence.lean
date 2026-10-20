/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange

@[expose] public section

universe u v

namespace CategoryTheory.FiberedCategoryOver.Groupoids

open scoped Bicategory

/-- In a square of morphisms of categories fibred in groupoids that commutes up to an
invertible `2`-cell, equivalences on the horizontal sides preserve and reflect relative
representability of the vertical morphisms. -/
theorem relativelyRepresentable.iff_of_equivalence
    {C : Type u} [Category.{v} C]
    {X' X Y' Y : FiberedCategoryOver.Groupoids.{u, v, max u v, v} C}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (eX : X' ≌ X) (eY : Y' ≌ Y) (η : eX.hom ≫ f ≅ f' ≫ eY.hom) :
    relativelyRepresentable f ↔ relativelyRepresentable f' := sorry

end CategoryTheory.FiberedCategoryOver.Groupoids
