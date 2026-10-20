module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

@[expose] public section

/-!
This module records universe-relative failures of smallness for Ext groups in
abelian categories.
-/

universe u

namespace CategoryTheory.Abelian

/-- There exists, in every universe level, an abelian category whose Ext groups
are not small in the corresponding morphism universe. -/
theorem exists_not_hasExt :
    ∃ (C : Type (u + 1)) (_ : Category.{u} C) (_ : Abelian C),
      ¬ HasExt.{u} C := sorry

end CategoryTheory.Abelian
