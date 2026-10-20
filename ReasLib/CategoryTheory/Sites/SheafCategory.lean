/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf

@[expose] public section

namespace CategoryTheory

universe u v w

/-- The category of sheaves is the full subcategory of presheaves satisfying the sheaf condition. -/
theorem sheaf_eq_fullSubcategory {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (A : Type w) [Category A] :
    Sheaf J A = ObjectProperty.FullSubcategory (Presheaf.IsSheaf J (A := A)) := sorry

end CategoryTheory
