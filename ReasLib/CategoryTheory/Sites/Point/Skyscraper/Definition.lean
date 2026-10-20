/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

@[expose] public section

open CategoryTheory GrothendieckTopology

universe u v w

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The set-valued skyscraper sheaf associated to a point and a set. -/
noncomputable abbrev setSkyscraperSheaf (Φ : Point.{w} J) (E : Type w) :
    Sheaf J (Type w) :=
  Φ.skyscraperSheaf E

end CategoryTheory.GrothendieckTopology.Point
