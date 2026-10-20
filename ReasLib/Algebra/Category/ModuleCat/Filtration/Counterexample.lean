/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import ReasLib.CategoryTheory.Filtration.Category
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Filtered Module Counterexamples

Structural limitations of the category of filtered module objects.
-/

@[expose] public section

open CategoryTheory

universe u

namespace ModuleCat.FilteredObject

/-- Example 12.3.13: for a nontrivial ring, the category of filtered modules is not abelian. -/
@[stacks 0108]
theorem not_nonempty_abelian (R : Type u) [Ring R] [Nontrivial R] :
    ¬ Nonempty (CategoryTheory.Abelian (CategoryTheory.FilteredObject (ModuleCat R))) := sorry

end ModuleCat.FilteredObject
