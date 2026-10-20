/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Zero morphisms for sheaf categories

The topological-space wrapper `TopCat.Sheaf` is definitionally the usual site-theoretic sheaf
category, but its `def` boundary prevents the generic full-subcategory zero-morphism instance
from being found automatically. This file exposes that canonical instance once for all
coefficient categories.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w u

namespace TopCat.Sheaf

variable {C : Type u} [Category.{w} C] [HasZeroMorphisms C]

/-- Sheaves valued in a category with zero morphisms inherit zero morphisms pointwise.
This is a fallback below the canonical zero morphisms induced by a preadditive structure. -/
instance (priority := 90) hasZeroMorphisms (X : TopCat.{w}) : HasZeroMorphisms (X.Sheaf C) :=
  inferInstanceAs
    (HasZeroMorphisms (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C))

end TopCat.Sheaf

end
