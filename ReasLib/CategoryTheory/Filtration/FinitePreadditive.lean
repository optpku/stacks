/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Finite
public import ReasLib.CategoryTheory.Filtration.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Preadditive Finite Filtered Objects

This module names the canonical preadditive presentation on the category of finite filtered
objects. Ordinary APIs use the canonical pointwise zero morphisms of the full subcategory.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.FilteredObject

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

namespace Finite

/-- The canonical preadditive structure on finite filtered objects, inherited from the
preadditive structure on all filtered objects. -/
@[stacks 0122 "finite filtered preadditive structure"]
noncomputable abbrev preadditive : Preadditive (FilteredObject.Finite.category C) :=
  inferInstance

end Finite

end CategoryTheory.FilteredObject
