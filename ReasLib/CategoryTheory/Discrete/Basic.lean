/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Basic instances for discrete categories

This leaf owns canonical instances for `CategoryTheory.Discrete`.
-/

@[expose] public section

universe w

namespace CategoryTheory

/-- A discrete category is nonempty whenever its type of objects is nonempty. -/
instance Discrete.instNonempty {α : Type w} [h : Nonempty α] : Nonempty (Discrete α) := by
  rcases h with ⟨a⟩
  exact ⟨Discrete.mk a⟩

end CategoryTheory
