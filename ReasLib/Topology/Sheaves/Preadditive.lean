/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Sectionwise preadditive structures on topological presheaves and sheaves

These instances expose the functor-category and full-subcategory structures through the
topological category definitions. Their low priority preserves mathlib's abelian instances
when those are available.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Addition of presheaf morphisms is defined sectionwise. -/
instance (priority := 100) Presheaf.preadditive (X : TopCat.{w}) :
    Preadditive (X.Presheaf C) :=
  inferInstanceAs (Preadditive ((Opens X)ᵒᵖ ⥤ C))

/-- Sheaves inherit sectionwise addition from the full subcategory of presheaves. -/
instance (priority := 100) Sheaf.preadditive (X : TopCat.{w}) :
    Preadditive (X.Sheaf C) :=
  inferInstanceAs (Preadditive (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C))

end TopCat
