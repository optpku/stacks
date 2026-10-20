/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.Sheaf

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v w

namespace TopCat

variable (X : TopCat.{u}) (C : Type v) [Category.{w} C]

/-- The topological-space sheaf category is the sheaf category on the opens Grothendieck
topology. -/
theorem sheaf_eq_siteSheaf :
    X.Sheaf C = CategoryTheory.Sheaf (Opens.grothendieckTopology X) C := rfl

end TopCat

end
