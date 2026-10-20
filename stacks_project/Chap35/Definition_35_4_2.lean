/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.Shapes.SplitEqualizer
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {A B D : C} {f : A ⟶ B} {g₁ g₂ : B ⟶ D}
variable (equalizes : f ≫ g₁ = f ≫ g₂)

/- Definition 35.4.2: a split equalizer is an equalizing diagram equipped with a
retraction of its equalizing map and a section of the second parallel map, satisfying
the compatibility between the two chosen splittings. -/
@[stacks 08WH] #check
  (CategoryTheory.IsSplitEqualizer.nonempty_iff_exists equalizes :
    Nonempty (CategoryTheory.IsSplitEqualizer g₁ g₂ f) ↔
      ∃ (h : B ⟶ A) (i : D ⟶ B),
        f ≫ h = 𝟙 A ∧ h ≫ f = g₁ ≫ i ∧ g₂ ≫ i = 𝟙 B)

end CategoryTheory
