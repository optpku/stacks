module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
import Mathlib.Tactic.CrossRefAttribute

/-!
# The perfect derived subcategory

The full subcategory of perfect objects is the common carrier for generation, compactness, and
Grothendieck-group constructions.

@stack 0AFY
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory

/-- The full subcategory of perfect objects in the derived category of `R`-modules. -/
@[stacks 0AFY "perfect derived subcategory"]
abbrev PerfectDerived (R : Type u) [Ring R] : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (DerivedCategory.IsPerfect :
      ObjectProperty (DerivedCategory (ModuleCat.{u} R)))

end CategoryTheory
