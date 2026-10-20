/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Grothendieck

@[expose] public section

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

/-- One Grothendieck topology is below another exactly when its covering sieves are
contained in those of the other topology at every object. -/
theorem le_iff_forall_subset {J₁ J₂ : GrothendieckTopology C} :
    J₁ ≤ J₂ ↔ ∀ U : C, J₁ U ⊆ J₂ U := sorry

end CategoryTheory.GrothendieckTopology
