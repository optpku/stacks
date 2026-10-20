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
