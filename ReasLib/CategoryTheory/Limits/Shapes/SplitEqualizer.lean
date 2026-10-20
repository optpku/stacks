/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.SplitEqualizer

@[expose] public section

universe v u

namespace CategoryTheory.IsSplitEqualizer

variable {C : Type u} [Category.{v} C]
variable {A B D : C} {f : A ⟶ B} {g₁ g₂ : B ⟶ D}

/-- Canonical split-equalizer data exists exactly when there are maps satisfying the three
splitting identities. -/
theorem nonempty_iff_exists (equalizes : f ≫ g₁ = f ≫ g₂) :
    Nonempty (CategoryTheory.IsSplitEqualizer g₁ g₂ f) ↔
      ∃ (h : B ⟶ A) (i : D ⟶ B),
        f ≫ h = 𝟙 A ∧ h ≫ f = g₁ ≫ i ∧ g₂ ≫ i = 𝟙 B := sorry

end CategoryTheory.IsSplitEqualizer
