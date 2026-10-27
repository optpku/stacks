/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

@[expose] public section

open CategoryTheory MonoidalCategory
universe v u
namespace CategoryTheory.MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The canonical multiplication of the tensor unit is invariant under braiding. -/
theorem braiding_unit_mul :
    (β_ (𝟙_ C) (𝟙_ C)).hom ≫ (λ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom := by
  rw [braiding_leftUnitor, unitors_equal]

/-- Moving the unit past the left factor and then removing it agrees with
removing it from the right factor; associators are explicit. -/
theorem tensor_leftUnitor_braiding (X Y : C) :
    X ◁ (λ_ Y).hom =
      (α_ X (𝟙_ C) Y).inv ≫ ((β_ X (𝟙_ C)).hom ▷ Y) ≫ ((λ_ X).hom ▷ Y) := sorry

end CategoryTheory.MonoidalCategory
