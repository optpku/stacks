/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Canonical

@[expose] public section

universe u v

namespace CategoryTheory.Sheaf

/-- The canonical topology is the greatest Grothendieck topology for which every
representable presheaf is a sheaf. -/
theorem isGreatest_canonicalTopology (C : Type u) [Category.{v} C] :
    IsGreatest {J : GrothendieckTopology C | ∀ X : C, Presieve.IsSheaf J (yoneda.obj X)}
      (canonicalTopology C) := sorry

end CategoryTheory.Sheaf
