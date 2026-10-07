module

public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
public import Mathlib.CategoryTheory.Groupoid.Discrete

/-!
# Locally discrete bicategories as `(2,1)`-categories

This support module records the general fact that promoting an ordinary category to a
locally discrete bicategory produces a locally groupoidal bicategory. It is useful whenever a
construction specializes one endpoint to an ordinary category without introducing nontrivial
`2`-cells.
-/

@[expose] public section

namespace CategoryTheory.Bicategory

universe u v

/-- The locally discrete bicategory associated to any category is locally groupoidal. -/
instance LocallyDiscrete.isLocallyGroupoid (C : Type u) [Category.{v} C] :
    IsLocallyGroupoid (LocallyDiscrete C) :=
  fun _ _ => inferInstance

end CategoryTheory.Bicategory
