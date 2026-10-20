/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Pullback.Pseudofunctor.Construction

/-!
# Ambient action computations for fixed-base pullback in groupoids

This leaf identifies the based-category-valued action before the groupoid-fibre property is
restored by the full-subbicategory lift.
-/

@[expose] public section

noncomputable section

universe uC uD uS vC vD vS

namespace CategoryTheory.FiberedCategoryOver.Groupoids.Pullback

open CategoryTheory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable (u : C ⥤ D)

/-- The object action of the ambient pseudofunctor is the underlying based category of the
neutral fibred-category pullback. -/
@[simp]
theorem ambient.obj
    (X : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D) :
    (ambient u).obj X =
      (FiberedCategoryOver.pullback u
        ((FiberedCategoryOver.Groupoids.toFibered D).obj X)).toBasedCategory := sorry

/-- The `1`-cell action of the ambient pseudofunctor is the underlying based pullback map. -/
@[simp]
theorem ambient.map
    {X Y : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D} (F : X ⟶ Y) :
    (ambient u).map F =
      FiberedCategoryOver.Pullback.basedMap u
        ((FiberedCategoryOver.Groupoids.toFibered D).map F) := sorry

/-- The `2`-cell action of the ambient pseudofunctor is the underlying based pullback natural
transformation. -/
@[simp]
theorem ambient.map₂
    {X Y : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (ambient u).map₂ eta =
      FiberedCategoryOver.Pullback.basedMap₂ u
        ((FiberedCategoryOver.Groupoids.toFibered D).map₂ eta) := sorry

end CategoryTheory.FiberedCategoryOver.Groupoids.Pullback

